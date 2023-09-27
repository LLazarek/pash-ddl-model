#lang at-exp racket

(require redex)

;; todo: add task parallelism
;;
;; I think that actually the place that this must happen is in the ↑ compilation
;; relation, because everything after operates on independent DFGs as separated
;; by that relation. Specifically, I think the right approach is to add a rule
;; like the `SeqBothBg`, but with these differences:
;;
;; 1. add one extra premise/constraint requiring that the intersection of
;;    `outputs(p_1)` and `inputs(p_2)` is empty
;; 2. remove the `bg` constraint on the compilation of `c_1` -- i.e. replace `bg` with `b`.

(define-language ddl
  [P ::= {I O E}]
  [I O ::= vars]
  [vars ::= [x ...]]
  [node ::= (vars ← f vars)]
  [E ::= [node ...]] ;; static program terms
  [x f ::= variable-not-otherwise-mentioned]

  [e ::= (s* ← f s*)] ;; dynamic program terms with concrete streams
  [s ::= [msg ...] s⊥]
  [s⊥ ::= [msg ... ⊥]]
  [msg ::= string]
  [msg-or-eof ::= msg ⊥]
  [s* ::= [s ...]]

  [choices ::= {natural ...}]

  [binding ::= (x ⟶ s)]
  [Γ ::= [binding ...]]
  [σ ::= [binding ...]]
  [state ::= {P ⊢ Γ σ}]

  #:binding-forms
  {[x_I ...] #:exports (shadow x_I ...) O [([x_out ...] #:exports (shadow x_out ...) ← f vars) ...] #:refers-to (shadow x_I ... (shadow x_out ...) ...)})

(default-language ddl)

(define-metafunction ddl
  ;; ++ corresponds to \cdot in icfp'21
  ++ : s s -> s
  [(++ [msg ...] [msg-or-eof ...])
   [msg ... msg-or-eof ...]])

#;(define-metafunction streams
  pass-message : (f s* s s s*) -> s*
  [(pass-message (f s*_before s_k s_new s*_after))
   s*_results

   (where s*_results ())])

(define-syntax-rule (define-binding-getter name map)
  (begin
    (define-metafunction ddl
      name : map vars -> s*
      [(name map vars)
       (internal map vars [])])
    (define-metafunction ddl
      internal : map vars s* -> s*
      [(internal map [x (... ...) x_next] [s (... ...)])
       (internal map [x (... ...)] [s_next s (... ...)])

       (where/error [_ (... ...) (x_next ⟶ s_next) _ (... ...)] map)]
      [(internal map [] s*)
       s*])))

;; (define-metafunction ddl
;;   bindings/Γ : (Γ vars) -> s*
;;   [(bindings/Γ (Γ vars))
;;    (bindings/Γ/internal (Γ vars []))])
;; (define-metafunction ddl
;;   bindings/Γ/internal : (Γ vars s*) -> s*
;;   [(bindings/Γ/internal (Γ [x ... x_next] [s ...]))
;;    (bindings/Γ/internal (Γ [x ...] [s_next s ...]))

;;    (where [_ ... (x_next ⟶ s_next) _ ...] Γ)]
;;   [(bindings/Γ/internal (Γ [] s*))
;;    s*])

(define-binding-getter bindings/Γ Γ)
(define-binding-getter bindings/σ σ)

(define-metafunction ddl
  update/Γ : Γ vars s* -> Γ
  [(update/Γ Γ [x ...] [s ...])
   (update/Γ/internal Γ [(x ⟶ s) ...])])
(define-metafunction ddl
  ;;                  current updates
  update/Γ/internal : Γ       Γ -> Γ
  [(update/Γ/internal [any_before
                       ...
                       (x ⟶ s_old)
                       any_after
                       ...]
                      [(x ⟶ s_new) any_more ...])
   (update/Γ/internal [any_before
                       ...
                       (x ⟶ s_new)
                       any_after
                       ...]
                      [any_more ...])]
  [(update/Γ/internal Γ [])
   Γ])

(define-syntax-rule (define-run/choice
                      run-name
                      choice-name
                      (op
                       [s*-ongoing #:choice choice-expr body ...]
                       [s*-end end-body ...])
                      ...)
  (begin
    (define-metafunction ddl
      run-name : f s* -> s*
      {~@
       [(run-f f s*-ongoing)
        body ...
        (side-condition (equal? (term f) 'op))]
       [(run-f f s*-end)
        end-body ...
        (side-condition (equal? (term f) 'op))]}
      ...)
    (define-metafunction ddl
      choice-name : f s* -> choices
      {~@
       [(choice f s*-ongoing)
        choice-expr
        (side-condition (equal? (term f) 'op))]
       [(choice f s*-end)
        {} ;; ensures part of the constraint under fig 3 (pg 10)
        (side-condition (equal? (term f) 'op))]}
      ...)))

(define-run/choice
  run-f choice
  (cat {[[msg_done ... ⊥] ... [msg_in_progress ...] s_todo ...]
        #:choice ,(list (length (term ([msg_done ...] ...))))
        [s_concat]
        (where s_concat [msg_done ... ... msg_in_progress ...])}
       {[[msg_done ... ⊥] ...]
        [s_concat]
        (where s_concat [msg_done ... ... ⊥])})

  (grep {[[msg_done ... ⊥] ... [msg_in_progress ...] s_todo ...]
        #:choice ,(list (length (term ([msg_done ...] ...))))
         [s_grepped]
         (where s_grepped ,(filter (λ (s) (string-contains? s "foo"))
                                   (term [msg_done ... ... msg_in_progress ...])))}
        {[[msg_done ... ⊥] ...]
         [[msg_grepped ... ⊥]]
         (where [msg_grepped ...] ,(filter (λ (s) (string-contains? s "foo"))
                                           (term [msg_done ... ...])))})

  (tee {[[msg_done ... ⊥] ... [msg_in_progress ...] s_todo ...]
        #:choice ,(list (length (term ([msg_done ...] ...))))
        [s_concat s_concat]
        (where s_concat [msg_done ... ... msg_in_progress ...])}
       {[[msg_done ... ⊥] ...]
        [s_concat s_concat]
        (where s_concat [msg_done ... ... ⊥])})

  (interleave {[s_l s_r]
               #:choice ,(list (if (<= (length (term s_l))
                                       (length (term s_r)))
                                   (if (member '⊥ (term s_l))
                                       1
                                       0)
                                   1))
               [,(interleave (term s_l) (term s_r))]}
              {[s⊥_l s⊥_r]
               [,(interleave (term s⊥_l) (term s⊥_r))]}))

(define (interleave l1 l2)
  (reverse
   (let loop ([res empty]
              [rest-l l1]
              [rest-r l2]
              [left? #t])
     (match rest-l
       [(or '() (cons '⊥ _))
        (append (reverse rest-r) res)]
       [(cons msg-l more-l)
        (if left?
            (loop (cons msg-l res)
                  more-l
                  rest-r
                  (not left?))
            (match rest-r
              [(or '() (cons '⊥ _))
               (append (reverse rest-l) res)]
              [(cons msg-r more-r)
               (loop (cons msg-r res)
                     rest-l
                     more-r
                     (not left?))]))]))))

(define-logger ddl)

(define ddl-red
  (reduction-relation
   ddl
   #:domain state

   (--> {{I O E} ⊢ Γ σ}
        {{I O E} ⊢
         (update/Γ Γ
                   [x_out ...]
                   [s_out_after_step ...])
         [binding_σ_<k
          ...
          (x_k ⟶ (++ s_k_before_step s_x_k_step_message))
          binding_σ_>k
          ...]}

        (where [_ ... ([x_out ...] ← f [x_in_<k ... x_k x_in_>k ...]) _ ...] E)
        (side-condition (log-ddl-debug @~a{
                                           E matches, with x_out... = @(term [x_out ...]), @;
                                           x_k = @(term x_k)}))
        (side-condition
         (log-ddl-debug @~a{
                            Checking that x_k is in the choice set of @(term f)... @;
                            @(length (term (x_in_<k ...))) @;
                            vs @(term (choice f (bindings/σ σ [x_in_<k ... x_k x_in_>k ...])))
                            }))
        ;; todo: see note below
        (side-condition (member (length (term (x_in_<k ...)))
                                (term (choice f (bindings/σ σ [x_in_<k ... x_k x_in_>k ...])))))

        (where/error [_ ... (x_k ⟶ s_k) _ ...] Γ)
        (side-condition (log-ddl-debug @~a{Γ matches, with s_k = @(term s_k)}))
        (where/error [binding_σ_<k ... (x_k ⟶ s_k_before_step) binding_σ_>k ...] σ)
        (side-condition
         (log-ddl-debug @~a{σ matches, with s_k_before_step = @(term s_k_before_step)}))
        (where [msg_k_before_step ...] s_k_before_step)
        (where [msg_k_before_step ... msg-or-eof msg-or-eof_k_more ...] s_k) ;; there must be a new message in `s_k`, otherwise can't step
        (where/error s_x_k_step_message [msg-or-eof])
        (side-condition
         (log-ddl-debug @~a{
                            splitting of s_k matches, @;
                            s_x_k_step_message = @(term s_x_k_step_message), @;
                            and remaining after that: @(term [msg-or-eof_k_more ...])}))

        (where/error [s_in_<k_σ ...] (bindings/σ σ [x_in_<k ...]))
        (where/error [s_in_>k_σ ...] (bindings/σ σ [x_in_>k ...]))
        (where/error [s_out_after_step ...] (run-f f [s_in_<k_σ ... (++ s_k_before_step s_x_k_step_message) s_in_>k_σ ...]))
        (side-condition
         (log-ddl-debug @~a{
                            ran @(term f) with the new s_x_k_step_message, @;
                            new s_out_after_step = @(term [s_out_after_step ...])
                            }))
        "step")))

;; The choice side condition is pretty subtle.
;; it seems the condition is important to constrain which input interleave consumes in the reduction rule here, and afaict the choice condition encodes that constraint
;; But actually it's doing something else here.
;; To see why, consider this program:
#;(term {{[stdin1 stdin2] [stdout] [([stdout] ← interleave [stdin1 stdin2])]}
         ⊢
         [(stdin1 ⟶ ["a" "b" ⊥]) (stdin2 ⟶ ["c" "d" ⊥]) (stdout ⟶ [])]
         [(stdin1 ⟶ []) (stdin2 ⟶ []) (stdout ⟶ [])]})
;;
;; If you check the traces, somehow the rules allow the Gamma to switch around arbitrarily inside a big lattice of non-deterministic reduction choices!
;; (e.g. step from (stdout ⟶ ["a" "c"]) to (stdout ⟶ ["a" "b" "c"]))
;; and restoring the choice side condition eliminates that behavior.
;; So clearly it plays a more subtle role here than I expected.


(module+ test
  (require rackunit)
  (check-true (redex-match? ddl s (term ["hello"])))
  (check-true (redex-match? ddl vars (term [stdout])))
  (check-true (redex-match? ddl vars (term [stdin])))
  (check-true (redex-match? ddl f (term cat)))
  (check-true (redex-match? ddl node (term ([stdout] ← cat [stdin]))))
  (check-true (redex-match? ddl Γ (term [(stdin ⟶ ["a" "b"])])))
  (check-true (redex-match? ddl state (term {{[stdin] [stdout] [([stdout] ← cat [stdin])]} ⊢ [(stdin ⟶ ["a" "b"]) (stdout ⟶ [])] [(stdin ⟶ []) (stdout ⟶ [])]})))

  (check-true (redex-match? ddl [_ ... ([x_out ...] ← f [x_in_<k ... x_k x_in_>k ...]) _ ...] (term [([stdout] ← cat [stdin])])))
  (check-true (redex-match? ddl [_ ... (stdin ⟶ ["a" "b"]) _ ...] (term [(stdin ⟶ ["a" "b"]) (stdout ⟶ [])])))
  (check-true (redex-match? ddl [s_out_before_step ...] (term (bindings/Γ [(stdin ⟶ ["a" "b"]) (stdout ⟶ [])] [stdout]))))
  (check-true (redex-match? ddl [[]] (term (bindings/Γ [(stdin ⟶ ["a" "b"]) (stdout ⟶ [])] [stdout]))))
  (check-true (redex-match? ddl [binding_σ_<k ... (stdin ⟶ []) binding_σ_>k ...] (term [(stdin ⟶ []) (stdout ⟶ [])])))
  (check-true (redex-match? ddl [msg msg_k_more ...] (term ["a" "b"])))
  (check-true (redex-match? ddl
                            [["a"]]
                            (term (run-f cat [["a"]]))))
  (check-true (redex-match? ddl
                            [["a" "b"]]
                            (term (run-f cat [["a" "b"] ["c"]]))))
  (check-true (redex-match? ddl
                            [["a" "b" "c"]]
                            (term (run-f cat [["a" "b" ⊥] ["c"]]))))
  (check-true (redex-match? ddl
                            {{I O E} ⊢ Γ σ}
                            (term {{[stdin] [stdout] [([stdout] ← cat [stdin])]} ⊢ [(stdin ⟶ ["a" "b"]) (stdout ⟶ [])] [(stdin ⟶ []) (stdout ⟶ [])]})))
  (test--> ddl-red
           (term {{[stdin] [stdout] [([stdout] ← cat [stdin])]}
                  ⊢
                  [(stdin ⟶ ["a" "b"]) (stdout ⟶ [])]
                  [(stdin ⟶ []) (stdout ⟶ [])]})
           (term {{[stdin] [stdout] [([stdout] ← cat [stdin])]}
                  ⊢
                  [(stdin ⟶ ["a" "b"]) (stdout ⟶ ["a"])]
                  [(stdin ⟶ ["a"]) (stdout ⟶ [])]}))
  (test--> ddl-red
           (term {{[stdin] [stdout] [([stdout] ← cat [stdin])]}
                  ⊢
                  [(stdin ⟶ ["a" "b"]) (stdout ⟶ ["a"])]
                  [(stdin ⟶ ["a"]) (stdout ⟶ [])]})
           (term {{[stdin] [stdout] [([stdout] ← cat [stdin])]}
                  ⊢
                  [(stdin ⟶ ["a" "b"]) (stdout ⟶ ["a" "b"])]
                  [(stdin ⟶ ["a" "b"]) (stdout ⟶ [])]}))
  (test--> ddl-red
           (term {{[stdin] [stdout] [([stdout] ← cat [stdin])]}
                  ⊢
                  [(stdin ⟶ ["a" "b" ⊥]) (stdout ⟶ ["a" "b"])]
                  [(stdin ⟶ ["a" "b"]) (stdout ⟶ [])]})
           (term {{[stdin] [stdout] [([stdout] ← cat [stdin])]}
                  ⊢
                  [(stdin ⟶ ["a" "b" ⊥]) (stdout ⟶ ["a" "b" ⊥])]
                  [(stdin ⟶ ["a" "b" ⊥]) (stdout ⟶ [])]}))
  (test-->> ddl-red
            (term {{[stdin] [stdout] [([stdout] ← cat [stdin])]}
                   ⊢
                   [(stdin ⟶ ["a" "b" ⊥]) (stdout ⟶ [])]
                   [(stdin ⟶ []) (stdout ⟶ [])]})
            (term {{[stdin] [stdout] [([stdout] ← cat [stdin])]}
                   ⊢
                   [(stdin ⟶ ["a" "b" ⊥]) (stdout ⟶ ["a" "b" ⊥])]
                   [(stdin ⟶ ["a" "b" ⊥]) (stdout ⟶ [])]}))

  (test-->> ddl-red
            (term {{[stdin1 stdin2] [stdout] [([stdout] ← cat [stdin2 stdin1])]}
                   ⊢
                   [(stdin1 ⟶ ["a" ⊥]) (stdin2 ⟶ ["b" ⊥]) (stdout ⟶ [])]
                   [(stdin1 ⟶ []) (stdin2 ⟶ []) (stdout ⟶ [])]})
            (term {{[stdin1 stdin2] [stdout] [([stdout] ← cat [stdin2 stdin1])]}
                   ⊢
                   [(stdin1 ⟶ ["a" ⊥]) (stdin2 ⟶ ["b" ⊥]) (stdout ⟶ ["b" "a" ⊥])]
                   [(stdin1 ⟶ ["a" ⊥]) (stdin2 ⟶ ["b" ⊥]) (stdout ⟶ [])]}))

  (test-->> ddl-red
            (term {{[stdin] [stdout] [([p1] ← cat [stdin])
                                      ([stdout] ← grep [p1])]}
                   ⊢
                   [(stdin  ⟶ ["a" "foo" ⊥])
                    (stdout ⟶ [])
                    (p1     ⟶ [])]
                   [(stdin  ⟶ [])
                    (stdout ⟶ [])
                    (p1     ⟶ [])]})
            (term {{[stdin] [stdout] [([p1] ← cat [stdin])
                                      ([stdout] ← grep [p1])]}
                   ⊢
                   [(stdin  ⟶ ["a" "foo" ⊥])
                    (stdout ⟶ ["foo" ⊥])
                    (p1     ⟶ ["a" "foo" ⊥])]
                   [(stdin  ⟶ ["a" "foo" ⊥])
                    (stdout ⟶ [])
                    (p1     ⟶ ["a" "foo" ⊥])]}))

  (check-equal? (interleave '() '()) '())
  (check-equal? (interleave '(1 2 3) '(a b c)) '(1 a 2 b 3 c))
  (check-equal? (interleave '(1 2 3) '(a b c d e)) '(1 a 2 b 3 c d e))
  (check-equal? (interleave '(1 2 3 4 5) '(a b c)) '(1 a 2 b 3 c 4 5))
  (check-equal? (term (choice interleave [[] []]))
                '(0))
  (check-equal? (term (choice interleave [["a"] []]))
                '(1))
  (check-equal? (term (choice interleave [[] ["a"]])) ;; couldn't actually happen
                '(0))
  (check-equal? (term (choice interleave [[⊥] ["a"]]))
                '(1))
  (check-equal? (term (choice interleave [[⊥] ["a" "c"]]))
                '(1))
  (test-->> ddl-red
            (term {{[stdin1 stdin2] [stdout] [([stdout] ← interleave [stdin1 stdin2])]}
                   ⊢
                   [(stdin1 ⟶ ["a" "b" ⊥]) (stdin2 ⟶ ["c" "d" ⊥]) (stdout ⟶ [])]
                   [(stdin1 ⟶ []) (stdin2 ⟶ []) (stdout ⟶ [])]})
            (term {{[stdin1 stdin2] [stdout] [([stdout] ← interleave [stdin1 stdin2])]}
                   ⊢
                   [(stdin1 ⟶ ["a" "b" ⊥]) (stdin2 ⟶ ["c" "d" ⊥]) (stdout ⟶ ["a" "c" "b" "d" ⊥])]
                   [(stdin1 ⟶ ["a" "b" ⊥]) (stdin2 ⟶ ["c" "d" ⊥]) (stdout ⟶ [])]}))

  (test-->> ddl-red
            (term {{[stdin1 stdin2] [stdout] [([stdout] ← interleave [stdin1 p1])
                                              ([p1] ← cat [stdin2])]}
                   ⊢
                   [(stdin1 ⟶ ["a" "b" ⊥]) (stdin2 ⟶ ["c" "d" ⊥]) (p1 ⟶ []) (stdout ⟶ [])]
                   [(stdin1 ⟶ []) (stdin2 ⟶ []) (p1 ⟶ []) (stdout ⟶ [])]})
            (term {{[stdin1 stdin2] [stdout] [([stdout] ← interleave [stdin1 p1])
                                              ([p1] ← cat [stdin2])]}
                   ⊢
                   [(stdin1 ⟶ ["a" "b" ⊥]) (stdin2 ⟶ ["c" "d" ⊥]) (p1 ⟶ ["c" "d" ⊥]) (stdout ⟶ ["a" "c" "b" "d" ⊥])]
                   [(stdin1 ⟶ ["a" "b" ⊥]) (stdin2 ⟶ ["c" "d" ⊥]) (p1 ⟶ ["c" "d" ⊥]) (stdout ⟶ [])]})))

(define-relation ddl
  complete? ⊆ P × Γ
  [(complete? {_ _ [_ ... ([x_out ...] ← f [x_in ...]) _ ...]}
              Γ)
   (where [s⊥_in ...] (bindings/Γ Γ [x_in ...]))
   (where [s⊥_out ...] (bindings/Γ Γ [x_out ...]))
   (side-condition (equal? (term [s⊥_out ...])
                           (term (run-f f [s⊥_in ...]))))])

(module+ test
  (test-judgment-holds
   (complete?
    {[stdin1 stdin2] [stdout] [([stdout] ← interleave [stdin1 p1])
                               ([p1] ← cat [stdin2])]}
    [(stdin1 ⟶ ["a" "b" ⊥]) (stdin2 ⟶ ["c" "d" ⊥]) (p1 ⟶ ["c" "d" ⊥]) (stdout ⟶ ["a" "c" "b" "d" ⊥])]))
  (check-false
   (judgment-holds (complete?
                    {[stdin] [stdout] [([stdout] ← cat [stdin])]}
                    [(stdin ⟶ ["a" "b"]) (stdout ⟶ ["a" "b"])]))))

;; note: substitution subtlety here; only read vars are substituted.
;; todo: perhaps this can be fixed with a better binding forms declaration?
(define-metafunction ddl
  substitute/node : node x x -> node
  [(substitute/node (vars_out ← f vars_in) x_from x_to)
   (vars_out ← f (substitute vars_in x_from x_to))])

(define-judgment-form ddl
  #:mode (aux-transform I O)
  #:contract (aux-transform P P)
  ;; renamed from the paper: x_i ⟶ x_read, x_j ⟶ x_fresh
  [(aux-transform {I O [node ...]}
                  {I O [node_subst ... ([x_fresh] ← relay [x_read])]})
   (where x_fresh (unused I O [node ...]))
   ;; todo note: x_read can't be universally quantified here -- the paper seems to be missing this condition
   (where [_ ... x_read _ ...] (used/read I O [node ...]))
   (side-condition ,(displayln @~a{Adding relay of @(term x_read)}))
   (where [node_subst ...] [(substitute/node node x_read x_fresh) ...])
   "relay-add"]
  [(aux-transform {I O [node_0 ... ([x_fresh] ← relay [x_read]) node_1 ...]}
                  {I O [node_0_subst ... node_1_subst ...]})
   (where [node_0_subst ...] [(substitute/node node_0 x_fresh x_read) ...])
   (where [node_1_subst ...] [(substitute/node node_1 x_fresh x_read) ...])
   "relay-cut"])

(define-metafunction ddl
  used/read : I O E -> vars
  [(used/read [x_I ...] O [(vars ← f [x_in ...]) ...])
   ,(remove-duplicates (term [x_I ... x_in ... ...]))])

(define-metafunction ddl
  unused : I O E -> x
  [(unused I O E)
   ,(gensym 'fresh)])

(module+ test
  (test-judgment-holds
   (aux-transform {[stdin] [stdout] [([stdout] ← cat [stdin])]}
                  {[stdin] [stdout] [([stdout] ← cat [x_fresh])
                                     ([x_fresh] ← relay [stdin])]}))
  (test-judgment-holds
   (aux-transform {[stdin] [stdout] [([stdout] ← cat [x_fresh])
                                     ([x_fresh] ← relay [stdin])]}
                  {[stdin] [stdout] [([stdout] ← cat [stdin])]}))
  (test-judgment-holds
   (aux-transform {[stdin] [stdout] [([stdout] ← cat [x_fresh])
                                     ([x_fresh] ← relay [stdin])]}
                  {[stdin] [stdout] [([stdout] ← cat [x_fresh])
                                     ([x_fresh] ← relay [x_fresh2])
                                     ([x_fresh2] ← relay [stdin])]}))
  )
