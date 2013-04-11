#lang racket/base

(provide make-queue
	 queue?
	 enqueue
	 enqueue-all
	 dequeue
	 list->queue
	 queue->list
	 queue-length
	 queue-empty?
	 queue-append
	 queue-extract)

(struct queue (head tail) #:transparent)

(define (make-queue)
  (queue '() '()))

(define (enqueue q v)
  (queue (queue-head q)
	 (cons v (queue-tail q))))

(define (enqueue-all q v)
  (queue (queue-head q)
	 (append (reverse v) (queue-tail q))))

(define (shuffle q)
  (if (null? (queue-head q))
      (queue (reverse (queue-tail q)) '())
      q))

(define (dequeue q)
  (let ((q1 (shuffle q)))
    (values (car (queue-head q1))
	    (queue (cdr (queue-head q1)) (queue-tail q1)))))

(define (list->queue xs)
  (queue xs '()))

(define (queue->list q)
  (append (queue-head q) (reverse (queue-tail q))))

(define (queue-length q)
  (+ (length (queue-head q))
     (length (queue-tail q))))

(define (queue-empty? q)
  (and (null? (queue-head q))
       (null? (queue-tail q))))

(define (queue-append q1 q2)
  (queue (append (queue-head q1)
		 (reverse (queue-tail q1))
		 (queue-head q2))
	 (queue-tail q2)))

(define (queue-extract q predicate [default-value #f])
  (let search-head ((head (queue-head q))
		    (rejected-head-rev '()))
    (cond
     ((null? head) (let search-tail ((tail (reverse (queue-tail q)))
				     (rejected-tail-rev '()))
		     (cond
		      ((null? tail) (values default-value q))
		      ((predicate (car tail)) (values (car tail)
						      (queue (queue-head q)
							     (append (reverse (cdr tail))
								     rejected-tail-rev))))
		      (else (search-tail (cdr tail) (cons (car tail) rejected-tail-rev))))))
     ((predicate (car head)) (values (car head)
				     (queue (append (reverse rejected-head-rev)
						    (cdr head))
					    (queue-tail q))))
     (else (search-head (cdr head) (cons (car head) rejected-head-rev))))))
