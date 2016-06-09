(define (domain smallroom)

   (:requirements :strips :typing)
   (:types pos )
   (:predicates (adj ?i ?j - pos) (at ?i - pos) (closed ?i - pos)

                (gold-at ?i - pos) (got-the-treasure)
                )
   (:constants

    p1-1
    p1-2

     - pos
   )

   (:action move
      :parameters (?i - pos ?j - pos )
      :precondition (and (adj ?i ?j) (at ?i)  )
      :effect  (and (not (at ?i)) (at ?j))
   )


   (:action open
      :parameters (?p - pos )
      :precondition (and (at ?p) (closed ?p) )
      :effect (and (not (closed ?p)))
   )


   (:action check
     :parameters (?pos - pos )
     :precondition (and (not (closed ?pos)) (at ?pos) )
     :observe (gold-at ?pos)
   )

   (:action grab
      :parameters (?i - pos )
      :precondition (and (at ?i) (gold-at ?i) (not (closed ?i)))
      :effect (and (got-the-treasure) (not (gold-at ?i)))
   )
)