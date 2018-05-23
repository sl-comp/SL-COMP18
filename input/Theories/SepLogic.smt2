(theory SepLogic

 :funs ((emp Bool)
        (sep Bool Bool Bool :left-assoc)
        (wand Bool Bool Bool :right-assoc)
        (par (A B) (pto A B Bool))
        (par (A) (nil A))
       )
)
