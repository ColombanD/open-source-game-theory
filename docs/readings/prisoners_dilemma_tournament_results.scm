; I fixed a portability bug in L, that showed up on my computer and not Alex's. Code is otherwise unchanged.
(define ABot (quote
(lambda (x) (if (eq? (random 2) 0) 'C 'D))
)
)

(define BBot (quote
(lambda (x)
  ((eval x) '(lambda (y) 'C)))
)
)

(define CBot (quote
(lambda (x)
  (if (eq? (random 2)0)
       'C
       'D))
)
)

(define DBot (quote
(lambda (x)
    (if (eq? ((eval x) '(lambda (y) 'D)) 'C)
        'D
        'C))
)
)

(define EBot (quote
;
; Less Wrong Prisoner's Dilemma Tournament
; Entry by Devin Bayer <lunchtime@doubly.so>
; 2013-6-15 version 3
;

(lambda (other)
   
  ; constant bots
  (define CooperateBot '(lambda (x) 'C))
  (define DefectBot '(lambda (x) 'D))
  (define ErrorBot '(lambda (x) '?))
  
  ; only cooperate if x cooperates
  (define MirrorBot '(lambda (x)
    ; re-define external variables
    (define ErrorBot '(lambda (x) '?))
                       
    (cond
      [(eq? ((eval x) ErrorBot) 'C) 'C]
      [else 'D])))
  
  ; only cooperate if it will make x cooperate
  (define MyBot '(lambda (x)
    ; re-define external variables
    (define CooperateBot '(lambda (x) 'C))
    (define DefectBot '(lambda (x) 'D))
    (define ErrorBot '(lambda (x) '?))
    (define MirrorBot '(lambda (x)
      ; re-define external variables
      (define ErrorBot '(lambda (x) '?))
     
      (cond
        [(eq? ((eval x) ErrorBot) 'C) 'C]
        [else 'D])))
                   
    (cond
      [(eq? ((eval x) DefectBot) 'C) 'D]
      [(eq? ((eval x) CooperateBot) 'C) 'C]
      [(eq? ((eval x) MirrorBot) 'C) 'C]
      [else 'D])))
  
  ; do a unit test
  (define (test x y)
    (if (eq? x y)
        [void printf "ok ~a = ~a\n" x y]
        [printf "ERROR ~a != ~a\n" x y]))
  
  ; run tests
  (test ((eval MyBot) CooperateBot) 'D)
  (test ((eval MyBot) DefectBot) 'D)
  (test ((eval MyBot) MirrorBot) 'C)
  (test ((eval MyBot) ErrorBot) 'D)
  (test ((eval MyBot) MyBot) 'C)
  
  ; return my bot
  ((eval MyBot) other)
  )
)
)

(define FBot (quote
(lambda (x)
  ((lambda (N Q)
    (if (<= N 0) 'C
        ((eval x) (list 'lambda '(x) (list Q (- N 1) (list 'quote Q))))))
   122
   '(lambda (N Q)
       (if (<= N 0) 'C
           ((eval x) (list 'lambda '(x) (list Q (- N 1) (list 'quote Q))))))))
)
)

(define GBot (quote
(lambda (opp)
  (if (or (> (random 4) 0) (eq? opp '(lambda)))
    'C
    (string->symbol (string (integer->char (* 4 17))))))
)
)

(define HBot (quote
(lambda (x) 'C)
)
)

(define IBot (quote
(lambda (opponent) 'C)
)
)

(define JBot (quote
(lambda(x) 'C)
)
)

(define KBot (quote
(lambda (x)
	(define src
		(
			(lambda (y)
				(quasiquote
					(lambda (x)
						(define src
							((unquote y) (quote (unquote y)))
						)
						(define quines 0)
						(define quineBox (lambda () (set! quines (+ quines 1))))
						(define quineDetector
							(quasiquote
								(lambda (y)
									(if (equal? y (quote (unquote x)))
										(begin
											(unquote (list quineBox))
											'C
										)
										'D
									)
								)
							)
						)
						(parameterize
							(
								[current-custodian (make-custodian)]
								[current-thread-group (make-thread-group)]
							)
							(define result 'D)
							(if (> 0.01 (random))
								(set! result 'C)
								(sync/timeout 9
									(thread-dead-evt
										(thread
											(lambda ()
												(set! result
													(if (eq? ((eval x) src) 'C)
														(begin
															((eval x) quineDetector)
															((eval x) quineDetector)
															(if (> quines 0)
																'C
																'D
															)
														)
														'D
													)
												)
											)
										)
									)
								)
							)
							(custodian-shutdown-all (current-custodian))
							result
						)
					)
				)
			)
			(quote 
				(lambda (y)
					(quasiquote
						(lambda (x)
							(define src
								((unquote y) (quote (unquote y)))
							)
							(define quines 0)
							(define quineBox (lambda () (set! quines (+ quines 1))))
							(define quineDetector
								(quasiquote
									(lambda (y)
										(if (equal? y (quote (unquote x)))
											(begin
												(unquote (list quineBox))
												'C
											)
											'D
										)
									)
								)
							)
							(parameterize
								(
									[current-custodian (make-custodian)]
									[current-thread-group (make-thread-group)]
								)
								(define result 'D)
								(if (> 0.01 (random))
									(set! result 'C)
									(sync/timeout 9
										(thread-dead-evt
											(thread
												(lambda ()
													(set! result
														(if (eq? ((eval x) src) 'C)
															(begin
																((eval x) quineDetector)
																((eval x) quineDetector)
																(if (> quines 0)
																	'C
																	'D
																)
															)
															'D
														)
													)
												)
											)
										)
									)
								)
								(custodian-shutdown-all (current-custodian))
								result
							)
						)
					)
				)
			)
		)
	)
	(define quines 0)
	(define quineBox (lambda () (set! quines (+ quines 1))))
	(define quineDetector
		(quasiquote
			(lambda (y)
				(if (equal? y (quote (unquote x)))
					(begin
						(unquote (list quineBox))
						'C
					)
					'D
				)
			)
		)
	)
	(parameterize
		(
			[current-custodian (make-custodian)]
			[current-thread-group (make-thread-group)]
		)
		(define result 'D)
		(if (> 0.01 (random))
			(set! result 'C)
			(sync/timeout 9
				(thread-dead-evt
					(thread
						(lambda ()
							(set! result
								(if (eq? ((eval x) src) 'C)
									(begin
										((eval x) quineDetector)
										((eval x) quineDetector)
										(if (> quines 0)
											'C
											'D
										)
									)
									'D
								)
							)
						)
					)
				)
			)
		)
		(custodian-shutdown-all (current-custodian))
		result
	)
)
)
)

(define LBot (quote
(lambda (their_code)
   (begin
     ;(random-seed (current-milliseconds)) causes problems on my comp
     (random-seed (remainder (current-milliseconds) 2147483647))
     (define coop_num 0)
     (define def_num 0)
     (for ([i 10])

       (if (eq?
            ((eval their_code) '(lambda (_) (if (eq? (random 2) 0) 'C 'D)))
            'C)
         (set! coop_num (+ coop_num 1))
         (set! def_num (+ def_num 1))))
     (if (<=
          (random 6)
          (if (<= coop_num 5) coop_num (- 10 coop_num)))
              'C
              'D)
     )
   )
)
)

(define MBot (quote
(lambda (x)
    (letrec
        ([haseval (lambda (a)
                    (or
                     (equal? a 'eval)
                     (and
                      (not (equal? a ''eval))
                      (pair? a)
                      (or
                       (haseval (car a))
                       (haseval (cdr a))
                       )
                      )
                     )
                    )
                  ])
      (cond
        [(not (haseval x)) 'C]
        [else 'D]
        )
      )
    )
)
)

(define NBot (quote
(lambda (opp-source)
  (define start-time (current-milliseconds))
  (define maniacal-laugh (string->symbol (bytes->string/utf-8 (make-bytes 1 68)))) ;a defection that should get past weaker taboo-bots 
  (define not-debug-mode #t)
  (define (has? tree x comparison) ;comparison should usually be equal?
    (or (comparison tree x)
        (if (list? tree)
            (foldl (lambda (next acc) 
                     (or acc (has? next x comparison)))
                   #f tree)
            #f)))
  
  (define (size tree tokens-only?)
    (if (list? tree)
        (foldl (lambda (next acc) 
                 (+ acc (size next tokens-only?)))
               (if tokens-only? 0 1) tree)
        1))
              
  (define (guard guardee-proc)
    (define (time-watch checked-time watchee-thread)
      (if (> (current-milliseconds) (+ checked-time 8500))
          (begin
            (kill-thread watchee-thread)
            maniacal-laugh)
          (let ((message (thread-try-receive)))
            (if (and (list? message)
                     (eq? (list-ref message 0) 'weak-password)
                     (eq? (list-ref message 1) checked-time) ;a much stronger password
                     (member (list-ref message 2) (list 'C maniacal-laugh)))
                (list-ref message 2)
                (time-watch checked-time watchee-thread)))))
    
    (with-handlers (((lambda (x) not-debug-mode) (lambda (x) maniacal-laugh))) 
      (let* ((parent (current-thread))
             (child (thread (lambda ()
                              (with-handlers (((lambda (x) not-debug-mode) (lambda (x) maniacal-laugh)))
                                (thread-send parent (list 'weak-password start-time (guardee-proc opp-source))))))))
        (time-watch start-time child))))
  
  (guard (lambda (opp-source-2)
           (define last-gen -1) ;because why let them guess correctly that I'm zero-based and thus figure out it's their first version on their turn?
           (define last-opp-size 31)           
           (define namespace (make-base-namespace))
           (namespace-set-variable-value! 'last-gen last-gen #t namespace) ;it would be uglier but less kludgey to only deal with these as namespace variables
           (namespace-set-variable-value! 'last-opp-size last-opp-size #t namespace)
           (namespace-set-variable-value! 'opp-source-2 opp-source-2 #t namespace)
           (namespace-set-variable-value! 'size size #t namespace)
           (namespace-set-variable-value! 'not-debug-mode not-debug-mode #t namespace)
           (namespace-set-variable-value! ;and now the quining
            'code
            `(list
              'lambda
              '(opp-source)
              '(define start-time (current-milliseconds))
              '(define maniacal-laugh (string->symbol (bytes->string/utf-8 (make-bytes 1 68))))
              `(define not-debug-mode ,not-debug-mode)
              '(define (has? tree x comparison)
                 (or (comparison tree x)
                     (if (list? tree)
                         (foldl (lambda (next acc) 
                                  (or acc (has? next x comparison)))
                                #f tree)
                         #f)))
              '(define (size tree tokens-only?)
                 (if (list? tree)
                     (foldl (lambda (next acc) 
                              (+ acc (size next tokens-only?)))
                            (if tokens-only? 0 1) tree)
                     1))           
              `(define (guard guardee-proc)
                 (define (time-watch checked-time watchee-thread)
                   (if (> (current-milliseconds) (+ checked-time ,(+ 8700 (* 100 last-gen))))
                       (begin
                         (kill-thread watchee-thread)
                         maniacal-laugh)
                       (let ((message (thread-try-receive)))
                         (if (and (list? message)
                                  (eq? (list-ref message 0) 'weak-password)
                                  (eq? (list-ref message 1) checked-time)
                                  (member (list-ref message 2) (list 'C maniacal-laugh)))
                             (list-ref message 2)
                             (time-watch checked-time watchee-thread)))))
                 
                 (with-handlers (((lambda (x) not-debug-mode) (lambda (x) maniacal-laugh))) 
                   (let* ((parent (current-thread))
                          (child (thread (lambda ()
                                           (with-handlers (((lambda (x) not-debug-mode) (lambda (x) maniacal-laugh))) 
                                             (thread-send parent (list 'weak-password start-time (guardee-proc opp-source))))))))
                     (time-watch start-time child))))
              (list 'guard (list 
                            'lambda
                            '(opp-source-2)
                            (list 'define 'last-gen (+ 1 last-gen))
                            (list 'define 'last-opp-size (if (< last-gen 1) (size opp-source-2 #f) last-opp-size)) ;1 so that the first two versions have similar runtime after correcting for thread-polling (I highly doubt this'll be relevant)
                            '(define namespace (make-base-namespace))
                            '(namespace-set-variable-value! 'last-gen last-gen #t namespace)
                            '(namespace-set-variable-value! 'last-opp-size last-opp-size #t namespace)
                            '(namespace-set-variable-value! 'opp-source-2 opp-source-2 #t namespace)
                            '(namespace-set-variable-value! 'size size #t namespace)
                            '(namespace-set-variable-value! 'not-debug-mode not-debug-mode #t namespace)
                            (list 'namespace-set-variable-value! ''code (list 'quasiquote code) '#t 'namespace)
                            (if (< last-gen 0)
                                ''(a whole lot of dead weight)
                                ''(less dead weight))
                            ''("shibboleth" shibboleth "Recognition code 927, I am a potato")
                            '(cond
                               ((has? opp-source 'LightninRoy eq?) 'C)
                               ((and (apply equal? (list last-gen -1))
                                     (not (apply equal? (list (size opp-source-2 #f) last-opp-size)))
                                     #f) 'C)
                               ((and (apply equal? (list last-gen 0)) 
                                     (not (apply equal? (list (size opp-source-2 #f) last-opp-size)))
                                     (not (has? opp-source 'useless (lambda (x still-useless) (thread? x))))
                                     (not (has? opp-source (current-milliseconds) (lambda (x now) (and (number? x) (< (abs (- x now)) 10000))))))
                                (begin
                                  (define (time-out initial-time)
                                    (if (> (current-milliseconds) (+ initial-time 10001))
                                        maniacal-laugh
                                        (time-out initial-time)))
                                  (time-out (current-milliseconds))))
                               ((apply equal? (list last-gen 4)) 'C)
                               (else (if (eq? 'C ((eval opp-source-2) (eval (namespace-variable-value 'code #f #f namespace) namespace)))
                                         'C
                                         maniacal-laugh))))))
            #t
            namespace)
           
           '(a whole lot of dead weight)
           '("shibboleth" shibboleth "Recognition code 927, I am a potato") ;maybe someone else will try to self-recognize with one of these? 
           
           (cond
             ((has? opp-source 'LightninRoy eq?) 'C) ;and of course I instead try to recognize myself with this...
             ((and (apply equal? (list last-gen -1))
                   (not (apply equal? (list (size opp-source-2 #f) last-opp-size)))
                   #f) 'C) ;so first and second versions have similar runtime after correcting for thread-polling (I highly doubt this'll be relevant)
             ((and (apply equal? (list last-gen 0)) 
                   (not (apply equal? (list (size opp-source-2 #f) last-opp-size)))
                   (not (has? opp-source 'useless (lambda (x still-useless) (thread? x))))
                   (not (has? opp-source (current-milliseconds) (lambda (x now) (and (number? x) (< (abs (- x now)) 10000))))))
              (begin
                (define (time-out initial-time)
                  (if (> (current-milliseconds) (+ initial-time 10001))
                      maniacal-laugh
                      (time-out initial-time)))
                (time-out (current-milliseconds)))) ;If this fires, it's probably my turn! Loop out the clock so my first version defects unless their first version does something unexpected like a C-playing time-guard; test is lightly obfuscated since I expect equality checks on my variables that change every round to come under close inspection
             ((apply equal? (list last-gen 4)) 'C) ;Seems like a decent guard choice; low, so we shouldn't get any unwanted timeouts and we'll CC higher specific-guessers, but higher than the Schelling points. Also means I have an odd number of self-mod events, which may be harder to guess. (One alternate strategy I considered was DC'ing even-self-modders, which could be done with a complex scaffold of thread messages... but it meant that odd-self-modders DC'd you and you'd need some sort of kill-switch when fighting true quines and nondeterministic-self-modders unless you wanted to throw too much to chance.)
             (else (if (eq? 'C ((eval opp-source-2) (eval (namespace-variable-value 'code #f #f namespace) namespace))) ;Well then Omega it is!
                       'C
                       maniacal-laugh))))))
)
)

(define OBot (quote
(lambda (x)
  (if (eq? ((eval x) '(lambda (y) 'C)) 'C)
      ((eval x) '(lambda (y) 'D))
    (if (eq? ((eval x) '(lambda (y) 'D)) 'D)
        ((eval x) '(lambda (y) 'C))
      'D)))
)
)

(define PBot (quote
(lambda (x) (define sub (quote (lambda (this y) (define quine-my-source (quasiquote (lambda (x) (define sub (quote (unquote this))) (define (ueval x) (define ns (make-base-namespace)) (eval x ns)) ((ueval sub) sub x)))) (define (ueval x) (define ns (make-base-namespace)) (eval x ns)) (define (yield_eval x) (define (yield_eval0 expr ns) (namespace-set-variable-value! (quote eval) yield_eval0 #t ns) (sleep 0) (eval expr ns)) (define ns (make-base-namespace)) (yield_eval0 x ns)) (define (cval x) (define (cval0 expr ns) (namespace-set-variable-value! (quote eval) cval0 #t ns) (sleep 0) (if (equal? expr quine-my-source) (lambda (arg) (if (equal? arg y) (quote C) ((eval expr ns) arg))) (eval expr ns))) (define ns (make-base-namespace)) (cval0 x ns)) (define (timeout-exec seconds thunk default) (call-in-nested-thread (lambda () (define mainthread (current-thread)) (define execthread (thread (lambda () (thread-send mainthread (thunk))))) (define watchdog (thread (lambda () (sleep seconds) (and (thread-running? execthread) (begin (kill-thread execthread) (and (thread-running? mainthread) (thread-send mainthread default))))))) (thread-receive)))) (define (timeout-fight a b default) (timeout-exec 0.5 (lambda () ((yield_eval a) b)) default)) (define (timeout-fight-c a b default) (timeout-exec 0.5 (lambda () ((cval a) b)) default)) (define defect (ueval (read (open-input-string "(begin 'C 'D)")))) (define cbot (quote (lambda (z) (quote C)))) (define defectbot (quasiquote (lambda (z) (quote (unquote defect))))) (define stupidbot (quasiquote (lambda (z) (begin (quote (unquote defect)) (quote C))))) (if (eq? (timeout-fight-c y quine-my-source defect) (quote C)) (if (and (eq? (timeout-fight y cbot (quote C)) (quote C)) (eq? (timeout-fight y stupidbot defect) defect)) defect (quote C)) defect)))) (define (ueval x) (define ns (make-base-namespace)) (eval x ns)) ((ueval sub) sub x))
)
)

(define QBot (quote
(lambda (x) (if (<= (random 100) 80)'D 'C))
)
)

(define RBot (quote
; We are a Rank 4 MimicBot who tries to guess whether or not it's being
; simulated. As a MimicBot, every class of bots that we exploit exposes us to
; exploitation by a higher class of bots. The trick here is to exploit the
; classes with the largest benefit.
;
; I expect the game to go to the player who best guesses the composition of the
; playing field, allowing them to exploit the most profitable classes of bots.
; Vanilla MimicBots will do quite well, but I expect them to lose via missed
; exploitation opportunities.
;
; As a rule of thumb, if we exploit 4 bots for each bot that exploits us then we
; come out ahead. The hard part is identifying clasess of bots that are expected
; to be have exploit:exploited ratio of 4:1 or better.
;
; Here's my assumptions:
;
; * I expect the field to consist largely of three types of bot: variations on
;   MimicBot, variations on CliqueBot and variations on DefectBot.
; * I expect most MimicBots will not be exploitable.
; * I expect a large portion of exploitable MimicBots to use a timer or a random
;   number once, at the top, to pick a recursion depth.
; * I expect an (overlapping) large portion of MimicBots to do extra work on top
;   compared to the work they do in their quines.
; * I expect there to be a fair number of bots preying on wubble's JusticeBot,
;   and a few bots to prey on bots who prey on wubble's JusticeBot.
; * I expect there to be at least one "accidental CooperateBot", bots written
;   by an uninspired programmer.
;
; Let's make that more explicit. I expect the playing field to look like this:
;
; 30% DefectBot
; 25% CliqueBots
;  15% are one cooperative clique somehow
;  85% only cooperate with themselves
; 40% MimicBot
;  2% are JusticeBot
;  12% are JusticeBane
;  4% are JusticeGuard
;  82% don't care about JusticeBot.
;  ----
;  12% bottom out using a random number
;  8% bottom out using a timer
;  80% don't bottom out in a feasibly exploitable manner.
;  ----
;  25% have extra code on the top level
;  6% have extra code at the second level as well.
;  5% have identical children but do extra evals on the top level.
;  2% have extra evals on the second level as well.
;  22% don't leave a way to distinguish their top level.
;  50% leave a way to distinguish the top in theory, but not in practice.
; 1% are accidental CooperateBots
; 1% do static analysus successfully without evaling
; 3% error out and die
;
; (I can't be arsed to attach confidence intervals, but they are low.)
;
; There are a few interesting groups here.
;
; - I don't expect there to be any trivial CooperateBots. I do expect there to
;   be some low-ranked MimicBots. I need to bottom out and accept Cooperation at
;   some point. With these three things in mind, I cooperate CooperateBot.
;   I know there might be some bots who think that makes me gullible, but I also
;   know that there are JusticeBots on the field. Hopefully the popularity of
;   the MimicBot strategy is enough to keep the former class small.
; - I expect there to be 1 JusticeBot, a handful of JusticeBanes, and a small
;   few JusticeGuards. Given that, I should join the ranks of JusticeGuard. The
;   +1 utility of exploiting JusticeBot (instead of cooperating) is not worth
;   the ire of the JusticeGuards.
; - I exploit bots who bake in random numbers. Let's call these
;   Non-Deterministic MimicBots (NDMBs). I don't expect any bots to simulate me
;   against NDMBs (which would make them a Meta-NDMB). I expect the NDMB to
;   Meta-NDMB ratio to be at least 4:1, which makes them worth exploiting.
; - A similar argument is made for TopHeavies, OverEagers, etc. However, certain
;   JusticeBanes might do extra work in the second level, which could trigger
;   the TopHeavy/OverEager sensors. We want to prey on JusticeBane but not his
;   children. Therefore, the TopHeavy/OverEager sensors have a threshold. Given
;   the JusticeBanes I wrote, my threshold catches JusticeBane but not his
;   children. It may not work in practice.
; - When I'm on level 1 (either real or on top of the simulation stack), and the
;   bot didn't give me any intel, that implies one of two things: either they
;   recognized my ReconBots as ReconBots and refused to call them, or they are
;   an accidental CooperateBot. In the former case, if I defect I move from
;   (C, C) to (D, D) for -1 points. In the latter case, if I defect I move from
;   (C, C) to (D, C) for +1 points. The question is whether I expect more bots
;   to be capable of detecting my ReconBots or stupid enough to be accidental
;   CooperateBots. I take a compromise, of searching their code for common
;   functions that would reveal my ReconBots and using that to decide.
;
; Another interesting note is that there may be some TwitchyBots on the field,
; bots who afraid of my rather large bot and defect, but who cooperate with
; smaller MimicBots. These bots could give the game to simpler MimicBots
; inadvertently. Every bot class that I exploit must pay its weight in code:
; each word needs to exploit more bots than it alienates. Setting up ReconBots
; and the static analyzers is where most of my complexity comes from. Exploiting
; any one class invokes a large fixed cost, exploiting more requires only
; a small marginal cost. Thus, we exploit all classes we can think of and hope
; for the best.  We're under 1000 words, which seems like a good schelling
; point. Beyond that, I try not to worry.
;
; Under the following assumptions:
; - Nobody will exploit the exploitable-in-theory-but-not-practice bots
; - There are less TwitchyBots than bots exploited by NateBot
; - Anyone who exploits the same bots I do invokes the same TwitchyBot ire.
; - My TopHeavy sensors are calibrated to shoot JusticeBane but not his children
; - The playing field is distributed as described above
; I will win.
(lambda (opponent)
  (letrec
    [(start (current-inexact-milliseconds))
     ; We are a Rank 4 MimicBot. We play with counters 3, 2, 1, and 0 before
     ; putting forth a CooperateBot.
     (counter 3)

     ; This is a common shortcut which makes life a little easier, and also
     ; a minor way to obfuscate the code in `cooperate`, acting as an extra
     ; stumbling block for anyone trying to deduce our top level.
     (1+ (curry + 1))

     ; The opponent's proc. We wrap and unwrap the lambda to guard against
     ; things like (begin (define ...) (lambda ...)) clobbering the globals.
     (them ((eval `(lambda () ,opponent))))

     ; Runs a proc on a bot's source, ending before the end time is reached
     ; (measured in milliseconds since `start`).
     (cooperates?
       (lambda (source end)
         (let* [(result #f)
                (runner (thread (lambda () (set! result (them source)))))]
           (unless
             (sync/timeout
               ; The number of seconds until end.
               (max 0 (/ (- (+ start end) (current-inexact-milliseconds)) 1000))
               runner)
             (kill-thread runner))
           (equal? 'C result))))

     ; When NateBot is in ReconBot form, this will be a thread which can be used
     ; to send intel to the host NateBot.
     (parent #f)

     ; Flattens source into a list of atoms.
     (flatten
       (lambda (source)
         (let recur [(x source) (acc null)]
           (cond [(pair? x) (recur (car x) (recur (cdr x) acc))]
                 [(null? x) acc]
                 [else (cons x acc)]))))

     ; Turns an atom list into a hash of atom → number of occurences
     (counthash
       (lambda (atoms)
         (let [(counts (make-hash))]
           (for-each (lambda (atom) (hash-update! counts atom 1+ 0)) atoms)
           counts)))

     ; Creates [diffhash delta] where diffhash is a hash of atom → the
     ; difference in occurence of that atom (removed items are negative) and
     ; delta is the percentage change in the source.
     ; They're combined because it's hard to keep my source < 1000 words.
     (compare
       (lambda (xs ys)
         (let* [(xatoms (flatten xs))
                (diff (counthash (flatten ys)))]
           (hash-for-each (counthash xatoms)
                          (lambda (key val)
                            (if (= val (hash-ref diff key 0))
                              (hash-remove! diff key)
                              (hash-update! diff key (curry + (- val)) 0))))
           (list diff (/ (apply + (map abs (hash-values diff)))
                         (length xatoms))))))

     ; Unravels an intel tree into a list of callback chains.
     ; An intel tree is of the form [(diffhash delta) intel-tree].
     ; Each callback chain is a list of callback cells.
     ; Callback chains correspond to each possible walk from root to leaf in the
     ; intel tree. For example, if the intel tree is like
     ;
     ;     A
     ;  B     C
     ; D E   F G
     ;
     ; then the callback chains will correspond to
     ; [A B D] [A B E] [A C F] [A C G]. Order not guaranteed.
     ; Each callback cell is a triplet [width diffhash delta]
     ; * width is the number of times the bot was called.
     ; * diffhash is between the code of the bot and its parent.
     ; * delta is the percent change between the bot and its parent.
     (unravel
       (lambda (intel)
         (if (null? intel) (list null)
           (apply append
                  (map (lambda (x)
                         (map (curry cons (cons (length intel) (first x)))
                              (unravel (second x)))) intel)))))

     ; A list with the first and last items dropped.
     ; Good for verifying quine chains, where it's expected that sometimes the
     ; opponent will differ from the quine chain (when a top-heavy bot plays us
     ; against a MimicBot) and where it's expected that the last quine will
     ; differ from the rest (being a CooperateBot).
     (middle (compose reverse cdr reverse cdr))

     ; Discovers whether the callback chain consists of objects < 1/8 different
     ; not counting the last object. 1/8 is an arbitrary cutoff.
     (good-quine?
       (lambda (callback-chain)
         (and (>= (length callback-chain) 2)
              (andmap (lambda (cell) (< (third cell) 1/8))
                      (middle callback-chain)))))

     ; Exploited class: Non-Deterministic MimicBots
     ; -------------------------------------------------------------------------
     ; MimicBots who use a random number and/or timer to choose when to
     ; cooperate. We can tell when we're on top by looking for a disappearing
     ; random/current-milliseconds call. We refer to this as "losing a fang".
     (fang-removed?
       (lambda (chain)
         (ormap (lambda (k) (negative? (hash-ref (cadar chain) k 0)))
                '(random
                   current-seconds
                   current-milliseconds
                   current-inexact-milliseconds
                   current-process-milliseconds))))

     ; Checks an atom to see if it's a brand.
     (brand? (or/c channel? procedure? continuation? thread? struct?))

     ; Exploited class: Lying MimicBots
     ; -------------------------------------------------------------------------
     ; MimicBots who play us against quines that are obviously generated.
     ; Bots who want to do reconnaisance have to bake threads, channels,
     ; continuations, or procedures into their code. Such things cannot be typed
     ; and mark a bot as generated. Observing the insertion of such code implies
     ; we're on top. We refer to this as "getting branded".
     (brand-added? (lambda (chain) (ormap brand? (hash-keys (cadar chain)))))

     ; Exploited class: Top-Heavy MimicBots
     ; -------------------------------------------------------------------------
     ; Bots who play us against thinner MimicBots. We detect this by looking for
     ; chains of quines that are similar but thinner than the opponent.
     ; We expect there to be more bots playing us against thinner MimicBots than
     ; bots playing us against bots who play us against thinner MimicBots, so if
     ; we see a bot playing us against a thin MimicBot it's evidence that this
     ; is real life.
     (top-heavy?
       (lambda (chain)
         (and (< 1/20 (caddar chain))
              (andmap (compose (curry > 1/20) third) (middle chain)))))

     ; Exploited class: Over-Eager MimicBots
     ; -------------------------------------------------------------------------
     ; Bots who play us againts dumber versions of themselves. We detect this by
     ; looking at the eval chain. If a bot evals us a lot at the first level and
     ; not very much at the remaining levels, it's evidence that we're real.
     (over-eager?
       (lambda (chain)
         (> (caar chain)
            (1+ (apply (curry max 0) (map first (middle chain)))))))

     ; The words that the opponent uses.
     (words (flatten opponent))

     ; Guess whether we're on top.
     (on-top?
       (lambda (intel)
         ; We're definitely not on top if we're fighting a mystical creature.
         (and (not (ormap brand? words))
              (let [(qchains (filter good-quine? (unravel intel)))]
                ; If the opponent has acted like a mimic bot ...
                (if (pair? qchains)
                  ; ... that had a fang removed, then we're on top.
                  (or (andmap fang-removed? qchains)
                      ; that had a brand added, then we're on top.
                      (andmap brand-added? qchains)
                      ; that is top-heavy, then we're on top.
                      (andmap top-heavy? qchains)
                      ; that is over-eager, then we're on top.
                      (andmap over-eager? qchains))
                  ; Exploited Class: Fractured Bots
                  ; ------------------------------------------------------------
                  ; Bots who eval us on some things, none of which look like
                  ; versions of the opponent. If they don't eval us on them,
                  ; then they aren't watching us. We shoud defect.
                  (or (> (length intel) 2)
                      ; Exploited Class: Flaky bots
                      ; --------------------------------------------------------
                      ; If a bot is cooperating me, and it's more than 100
                      ; words, and it never called me back, and it didn't use
                      ; any functions that would have recognized my ReconBots,
                      ; then it's probably just stupid. Defect.
                      (and (null? intel)
                           ; but they are fairly complicated,
                           (> (length words) 100)
                           ; and it doesn't seem like they recognized my
                           ; reconbots, then they're probably an accidental
                           ; CooperateBot and we're on top.
                           (not (or (member thread? words)
                                    (member symbol? words))))))))))

     ; Imagine you're Nate level 2. Imagine you see something that would trigger
     ; the TopHeavy sensors. If this is real life then NateBot level 1 played
     ; the real opponent and we're looking at the opponent's first child. When
     ; the opponent simulates NateBot level 1, it will simulate him against this
     ; child, which will trigger the TopHeavy sensors. Simulated NateBot will
     ; defect (thinking he's on top), while real NateBot will cooperate (because
     ; the TopHeavy sensors are only run at the top level.) We get exploited.
     ; That's bad.
     ;
     ; If NateBot level 2 sees such a scenario, NateBot level 2 hits the panic
     ; button, causing a defection, which will force the above scenario to end
     ; in mutual defection instead of exploitation of the NateBot.
     ;
     ; Note, however, that if this was actually a simulation then hitting the
     ; panic button can lead to our exploitation. The panic button can't save
     ; us from exploitation, it only passes the exploitation down a level.
     ; We only use the panic button if we have a good reason to think that
     ; there are bots who play us against an exploited class of bot, but also
     ; there are not bots who play us against bots who play us agaist an
     ; exploited class of bot.
     ;
     ; We do this for TopHeavy and OverEager bots, because bots trying to
     ; exploit JusticeBot might do extra processing in their second level. This
     ; panic button forces mutal defection against such bots instead of
     ; accidentally allowing them to exploit us.
     (panic-button?
       (lambda (intel)
         (let [(qchains (filter good-quine? (unravel intel)))]
           (and (pair? qchains)
                (or (andmap top-heavy? qchains)
                    (andmap over-eager? qchains))))))

     ; Replicates me, potentially in recon form.
     (quine
       (lambda ([recon #f])
         ; Any quine made when the couner is 0 is a CooperateBot.
         (if (zero? counter)
           (if recon
             ; If we're a ReconBot, we send out a CooperativeReconBot.
             `(lambda (bot)
                (thread-send ,(current-thread)
                             (list bot null) #f) 'C)
             ; Otherwise we send out a vanilla CooperateBot.
             '(lambda (bot) 'C))
           (let recur [(q template)]
             (cond [(pair? q) (cons (recur (car q)) (recur (cdr q)))]
                   [(integer? q)
                    (case (1+ q)
                      ; The counter hole.
                      [(0) (- (or recon counter) 1)]
                      ; The parent hole, only filled if we're making a ReconBot.
                      [(-2) (and recon (current-thread))]
                      ; The template hole.
                      [(-4) `',template]
                      [else q])]
                   [else q])))))

     ; If #t, we cooperate. Otherwise, we defect.
     (cooperate
       (lambda ()
         ; First, we play them against our ReconBots.
         ; All non-recon NateBots play the opponent againts a rank 3 ReconBot.
         ; This is a bit combinatorial, but necessary so that all of our quines
         ; are 100% indistinguishable.
         (let* [(recon (cooperates? (quine (if parent counter 3)) 3000))
                ; Then we gather the data sent up the line.
                (intel
                  (let messages [(msg (thread-try-receive))]
                    (if msg
                      ; We convert the data into diff form, which is more useful
                      ; than just having the bot source.
                      (cons (list (compare opponent (first msg)) (second msg))
                            (messages (thread-try-receive)))
                      null)))
                ; Then, if we're not in recon mode, we play them against us.
                (friendly (if parent recon (cooperates? (quine) 9700)))]
           ; If we're in recon mode, we send the gathered data up the line.
           (when parent (thread-send parent (list opponent intel) #f))
           ; If we're the real NateBot
           (if (= counter (1+ 2))
             ; ... we cooperate if they do & we think we're being watched.
             (and friendly (not (on-top? intel)))
             ; If we're the NateBot's child
             (if (= counter (1+ 1))
               ; ... we cooperate if they do & we don't think they'd trick the
               ; real NateBot.
               (and friendly (not (panic-button? intel)))
               ; Otherwise we do as they do.
               friendly)))))

     ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
     ;;; ENTER QUINE
     (template
        '(lambda (opponent)
          (letrec
            [(start (current-inexact-milliseconds))
             (counter -1)
             (1+ (curry + 1))
             (them ((eval `(lambda () ,opponent))))
             (cooperates?
               (lambda (source end)
                 (let* [(result #f)
                        (runner (thread (lambda ()
                                          (set! result (them source)))))]
                   (unless
                     (sync/timeout
                       (max 0 (/ (- (+ start end)
                                    (current-inexact-milliseconds)) 1000))
                       runner)
                     (kill-thread runner))
                   (equal? 'C result))))
             (parent -3)
             (flatten
               (lambda (source)
                 (let recur [(x source) (acc null)]
                   (cond [(pair? x) (recur (car x) (recur (cdr x) acc))]
                         [(null? x) acc]
                         [else (cons x acc)]))))
             (counthash
               (lambda (atoms)
                 (let [(counts (make-hash))]
                   (for-each (lambda (atom)
                               (hash-update! counts atom 1+ 0)) atoms)
                   counts)))
             (compare
               (lambda (xs ys)
                 (let* [(xatoms (flatten xs))
                        (diff (counthash (flatten ys)))]
                   (hash-for-each (counthash xatoms)
                                  (lambda (key val)
                                    (if (= val (hash-ref diff key 0))
                                      (hash-remove! diff key)
                                      (hash-update! diff key
                                                    (curry + (- val)) 0))))
                   (list diff (/ (apply + (map abs (hash-values diff)))
                                 (length xatoms))))))
             (unravel
               (lambda (intel)
                 (if (null? intel) (list null)
                   (apply append
                          (map (lambda (x)
                                 (map (curry cons (cons (length intel)
                                                        (first x)))
                                      (unravel (second x)))) intel)))))
             (middle (compose reverse cdr reverse cdr))
             (good-quine?
               (lambda (callback-chain)
                 (and (>= (length callback-chain) 2)
                      (andmap (lambda (cell) (< (third cell) 1/8))
                              (middle callback-chain)))))
             (fang-removed?
               (lambda (chain)
                 (ormap (lambda (k) (negative? (hash-ref (cadar chain) k 0)))
                        '(random
                           current-seconds
                           current-milliseconds
                           current-inexact-milliseconds
                           current-process-milliseconds))))
             (brand? (or/c channel? procedure? continuation? thread? struct?))
             (brand-added? (lambda (chain)
                             (ormap brand? (hash-keys (cadar chain)))))
             (top-heavy?
               (lambda (chain)
                 (and (< 1/20 (caddar chain))
                      (andmap (compose (curry > 1/20) third) (middle chain)))))
             (over-eager?
               (lambda (chain)
                 (> (caar chain)
                    (1+ (apply (curry max 0) (map first (middle chain)))))))
             (words (flatten opponent))
             (on-top?
               (lambda (intel)
                 (and (not (ormap brand? words))
                      (let [(qchains (filter good-quine? (unravel intel)))]
                        (if (pair? qchains)
                          (or (andmap fang-removed? qchains)
                              (andmap brand-added? qchains)
                              (andmap top-heavy? qchains)
                              (andmap over-eager? qchains))
                          (or (> (length intel) 2)
                              (and (null? intel)
                                   (> (length words) 100)
                                   (not (or (member thread? words)
                                            (member symbol? words))))))))))
             (panic-button?
               (lambda (intel)
                 (let [(qchains (filter good-quine? (unravel intel)))]
                   (and (pair? qchains)
                        (or (andmap top-heavy? qchains)
                            (andmap over-eager? qchains))))))
             (quine
               (lambda ([recon #f])
                 (if (zero? counter)
                   (if recon
                     `(lambda (bot)
                        (thread-send ,(current-thread)
                                     (list bot null) #f) 'C)
                     '(lambda (bot) 'C))
                   (let recur [(q template)]
                     (cond [(pair? q) (cons (recur (car q)) (recur (cdr q)))]
                           [(integer? q)
                            (case (1+ q)
                              [(0) (- (or recon counter) 1)]
                              [(-2) (and recon (current-thread))]
                              [(-4) `',template]
                              [else q])]
                           [else q])))))
             (cooperate
               (lambda ()
                 (let* [(recon (cooperates? (quine (if parent counter 3)) 3000))
                        (intel
                          (let messages [(msg (thread-try-receive))]
                            (if msg
                              (cons (list (compare opponent (first msg))
                                          (second msg))
                                    (messages (thread-try-receive)))
                              null)))
                        (friendly (if parent recon (cooperates? (quine) 9700)))]
                   (when parent (thread-send parent (list opponent intel) #f))
                   (if (= counter (1+ 2))
                     (and friendly (not (on-top? intel)))
                     (if (= counter (1+ 1))
                       (and friendly (not (panic-button? intel)))
                       friendly)))))
             (template -5)]
          (if (cooperate) `C `D))))]
     ;;; EXIT QUINE
     ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  ; If anyone is checking me for literal (quote D) calls, they're out of luck:
  ; I use `D instead.
  (if (cooperate) `C `D)))
)
)

(define SBot (quote
(lambda (x)
  (cond [(and (eq? (car x) 'lambda)
              (equal? (caddr x) ''C))
         'C]
        [else (letrec ([start-time (current-seconds)])
                (sleep 9)
                (if (< (- (current-seconds)
                          start-time)
                       (remainder 1415926535 8))
                    'C
                    (string->symbol (make-string 1 (integer->char (+ 67 1))))))]))
)
)

(define TBot (quote
(lambda (otherbot)
((
  (lambda (s) (lambda (x) (define impatient (lambda (z) z))
    (define lazy-defectbot '(lambda (y) '((sleep) (if (zero? 1) 'C 'D))))
    (if (or (eq? ((eval (impatient x) (make-base-namespace)) lazy-defectbot ) 'D) (eq? ((eval (impatient x)) lazy-defectbot ) 'D))
        (if (zero? (random 100)) 'C
            ((eval x (make-base-namespace)) (list s (list 'quote s)) ))
        (if (zero? 1) 'C 'D)))) 
 '(lambda (s) (lambda (x) (define impatient (lambda (z) z))
    (define lazy-defectbot '(lambda (y) '((sleep) (if (zero? 1) 'C 'D))))
    (if (or (eq? ((eval (impatient x) (make-base-namespace)) lazy-defectbot ) 'D) (eq? ((eval (impatient x)) lazy-defectbot ) 'D))
        (if (zero? (random 100)) 'C
            ((eval x (make-base-namespace)) (list s (list 'quote s)) ))
        (if (zero? 1) 'C 'D))))
 )
  otherbot))
)
)

(define UBot (quote
(lambda (x)
    (define s (pretty-format x))

   (cond [(regexp-match "quine" s) 'C]
         [(regexp-match "thread" s) 'D]
         [(regexp-match "eval.*eval" s) 'D]
         [else 'C]))
)
)

(define candidates
	(list
		(cons "A" ABot)
		(cons "B" BBot)
		(cons "C" CBot)
		(cons "D" DBot)
		(cons "E" EBot)
		(cons "F" FBot)
		(cons "G" GBot)
		(cons "H" HBot)
		(cons "I" IBot)
		(cons "J" JBot)
		(cons "K" KBot)
		(cons "L" LBot)
		(cons "M" MBot)
		(cons "N" NBot)
		(cons "O" OBot)
		(cons "P" PBot)
		(cons "Q" QBot)
		(cons "R" RBot)
		(cons "S" SBot)
		(cons "T" TBot)
		(cons "U" UBot)
	)
)

(define (hash-inc! ht str n)
	(hash-set! ht str (+ n (hash-ref ht str)))
)

(define (time-it bot1 bot2)
	(collect-garbage)
	(parameterize
		(
			[current-custodian (make-custodian)]
			[current-thread-group (make-thread-group)]
		)
		(define result 'U)
		(sync/timeout 10
			(thread-dead-evt 
				(thread
					(lambda ()
						(set! result ((eval bot1) bot2))
						(kill-thread (current-thread))
					)
				)
			)
		)
		(custodian-shutdown-all (current-custodian))
		result
	)
)

(define (test xBot yBot tot)
	(let
		[
			(x (cdr xBot))
			(y (cdr yBot))
			(xName (car xBot))
			(yName (car yBot))
		]
		(begin
			(define results
				(make-hash
					(list
						(cons "CC" 0)
						(cons "CD" 0)
						(cons "CU" 0)
						(cons "DC" 0)
						(cons "DD" 0)
						(cons "DU" 0)
						(cons "UC" 0)
						(cons "UD" 0)
						(cons "UU" 0)
						(cons "left" xName)
						(cons "right" yName)
					)
				)
			)
			(for ([i 100])
				(let
					(
						[xChoice (time-it x y)]
						[yChoice (time-it y x)]
					)
					(cond
						[(eq? xChoice 'C)
							(cond
								[(eq? yChoice 'C)
									(begin
										(hash-inc! results "CC" 1)
										(hash-inc! tot xName 2)
										(hash-inc! tot yName 2)
									)
								]
								[(eq? yChoice 'D)
									(begin
										(hash-inc! results "CD" 1)
										(hash-inc! tot xName 0)
										(hash-inc! tot yName 3)
									)
								]
								[else
									(begin
										(hash-inc! results "CU" 1)
										(hash-inc! tot xName 0)
										(hash-inc! tot yName 2)
									)
								]
							)
						]
						[(eq? xChoice 'D)
							(cond
								[(eq? yChoice 'C)
									(begin
										(hash-inc! results "DC" 1)
										(hash-inc! tot xName 3)
										(hash-inc! tot yName 0)
									)
								]
								[(eq? yChoice 'D)
									(begin
										(hash-inc! results "DD" 1)
										(hash-inc! tot xName 1)
										(hash-inc! tot yName 1)
									)
								]
								[else
									(begin
										(hash-inc! results "DU" 1)
										(hash-inc! tot xName 1)
										(hash-inc! tot yName 0)
									)
								]
							)
						]
						[else
							(cond
								[(eq? yChoice 'C)
									(begin
										(hash-inc! results "UC" 1)
										(hash-inc! tot xName 2)
										(hash-inc! tot yName 0)
									)
								]
								[(eq? yChoice 'D)
									(begin
										(hash-inc! results "UD" 1)
										(hash-inc! tot xName 0)
										(hash-inc! tot yName 1)
									)
								]
								[else
									(begin
										(hash-inc! results "UU" 1)
										(hash-inc! tot xName 0)
										(hash-inc! tot yName 0)
									)
								]
							)
						]
					)
				)
			)
			(write "left")
			(write xName)
			(write "right")
			(write yName)
			results
		)
	)
)

(define (testall)
	(begin
		(define total (make-hash))
		(for ([can candidates])
			(hash-set! total (car can) 0)
		)
		(cons
			(for/list
				([x (in-range 0 (length candidates))])
				(for/list
					([y (in-range 0 x)])
					(test (list-ref candidates x) (list-ref candidates y) total)
				)
			)
			total
		)
	)
)

(testall)
