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

(define-metafunction ddl
  run-f : f s* -> s*
  [(run-f f [[msg_done ... ⊥] ... [msg_in_progress ...] s_todo ...])
   [s_concat]
   (where s_concat [msg_done ... ... msg_in_progress ...])
   (side-condition (equal? (term f) 'cat))]
  [(run-f f [[msg_done ... ⊥] ...])
   [s_concat]
   (where s_concat [msg_done ... ... ⊥])
   (side-condition (equal? (term f) 'cat))]
  [(run-f f [[msg_done ... ⊥] ... [msg_in_progress ...] s_todo ...])
   [s_grepped]
   (where s_grepped ,(filter (λ (s) (string-contains? s "foo"))
                             (term [msg_done ... ... msg_in_progress ...])))
   (side-condition (equal? (term f) 'grep))]
  [(run-f f [[msg_done ... ⊥] ...])
   [[msg_grepped ... ⊥]]
   (where [msg_grepped ...] ,(filter (λ (s) (string-contains? s "foo"))
                                     (term [msg_done ... ...])))
   (side-condition (equal? (term f) 'grep))]
  [(run-f f [[msg_done ... ⊥] ... [msg_in_progress ...] s_todo ...])
   [s_concat s_concat]
   (where s_concat [msg_done ... ... msg_in_progress ...])
   (side-condition (equal? (term f) 'tee))]
  [(run-f f [[msg_done ... ⊥] ...])
   [s_concat s_concat]
   (where s_concat [msg_done ... ... ⊥])
   (side-condition (equal? (term f) 'tee))])


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

        (where [_ ... ([x_out ...] ← f [x_in_before ... x_k x_in_after ...]) _ ...] E)
        (side-condition (log-ddl-debug @~a{E matches, with x_out... = @(term [x_out ...]), x_k = @(term x_k)}))
        (where/error [_ ... (x_k ⟶ s_k) _ ...] Γ)
        (side-condition (log-ddl-debug @~a{Γ matches, with s_k = @(term s_k)}))
        (where/error [binding_σ_<k ... (x_k ⟶ s_k_before_step) binding_σ_>k ...] σ)
        (side-condition (log-ddl-debug @~a{σ matches, with s_k_before_step = @(term s_k_before_step)}))
        (where [msg_k_before_step ...] s_k_before_step)
        (where [msg_k_before_step ... msg-or-eof msg-or-eof_k_more ...] s_k) ;; there must be a new message in `s_k`, otherwise can't step
        (where/error s_x_k_step_message [msg-or-eof])
        (side-condition (log-ddl-debug @~a{splitting of s_k matches, s_x_k_step_message = @(term s_x_k_step_message), and remaining after that: @(term [msg-or-eof_k_more ...])}))

        (where/error [s_in_before ...] (bindings/σ σ [x_in_before ...]))
        (where/error [s_in_after ...] (bindings/σ σ [x_in_after ...]))
        (where/error [s_out_after_step ...] (run-f f [s_in_before ... (++ s_k_before_step s_x_k_step_message) s_in_after ...]))
        (side-condition (log-ddl-debug @~a{Ran @(term f) with the new s_x_k_step_message new s_out_after_step = @(term [s_out_after_step ...])}))
        "step")))


(module+ test
  (require rackunit)
  (check-true (redex-match? ddl s (term ["hello"])))
  (check-true (redex-match? ddl vars (term [stdout])))
  (check-true (redex-match? ddl vars (term [stdin])))
  (check-true (redex-match? ddl f (term cat)))
  (check-true (redex-match? ddl node (term ([stdout] ← cat [stdin]))))
  (check-true (redex-match? ddl Γ (term [(stdin ⟶ ["a" "b"])])))
  (check-true (redex-match? ddl state (term {{[stdin] [stdout] [([stdout] ← cat [stdin])]} ⊢ [(stdin ⟶ ["a" "b"]) (stdout ⟶ [])] [(stdin ⟶ []) (stdout ⟶ [])]})))

  (check-true (redex-match? ddl [_ ... ([x_out ...] ← f [x_in_before ... x_k x_in_after ...]) _ ...] (term [([stdout] ← cat [stdin])])))
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
                    (p1     ⟶ ["a" "foo" ⊥])]})))
