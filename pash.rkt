#lang at-exp racket

(require redex)

(define-language ddl
  [P ::= {I O E}]
  [I O ::= vars]
  [vars ::= [x ...]]
  [node ::= (vars ← f vars)]
  [E ::= [node ...]] ;; static program terms
  [x f ::= variable-not-otherwise-mentioned]

  [e ::= (s* ← f s*)] ;; dynamic program terms with concrete streams
  [s ::= [msg ... ⊥] [msg ...]]
  [msg ::= string]
  [msg-or-eof ::= msg ⊥]
  [s* ::= [s ...]]

  [choices ::= {natural ...}]

  [binding ::= (x ⟶ s)]
  [Γ ::= [binding ...]]
  [σ ::= [binding ...]]
  [state ::= {P ⊢ Γ σ}])

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
              {[[msg_done_l ... ⊥] [msg_done_r ... ⊥]]
               [,(interleave (term [msg_done_l ... ⊥])
                            (term [msg_done_r ... ⊥]))]}))

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
                   [(stdin1 ⟶ ["a" "b" ⊥]) (stdin2 ⟶ ["c" "d" ⊥]) (stdout ⟶ [])]})))
