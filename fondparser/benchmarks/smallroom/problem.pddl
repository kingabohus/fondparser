(define (problem smallroom-5)
(:domain smallroom)


   (:init
    (and
     (at p1-1)

     (closed p1-1)
     (closed p1-2)


     (adj p1-1 p1-2)
     (adj p1-2 p1-1)


     (oneof
       (gold-at p1-2)
       (gold-at p1-1)
     )

     )
    )
      (:goal (and (got-the-treasure) ) )
)
