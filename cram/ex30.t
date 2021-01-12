Tests keeping the event axiom "folded"...
  $ cervino -c prop ex30.cervino
  cervino (C) 2020 ONERA (development version)
  sort A
  sort B
  
  relation p in A
  axiom {
    G (some _s_B1: B | (some _s_A1: A | (some _s_A2: A |
     ((((!p(_s_A2) || p'(_s_A2)) && (!p'(_s_A2) || p(_s_A2))) &&
       ((!p(_s_A1) || p'(_s_A1)) && (!p'(_s_A1) || p(_s_A1))))
      ||
      (((!p(_s_A2) || p'(_s_A2)) && (!p'(_s_A2) || p(_s_A2))) &&
       ((!p(_s_A1) || p'(_s_A1)) && (!p'(_s_A1) || p(_s_A1)))))))) }
  axiom { false }
  axiom { true }
  check prop { false }
  assuming { true } using TFC[]
...vs unfolded on two constants per existential bound variable under G
  $ cervino -cu prop ex30.cervino
  cervino (C) 2020 ONERA (development version)
  sort A
  sort B
  constant _s_A2_5 in A
  constant _s_A2_4 in A
  constant _s_A1_3 in A
  constant _s_A1_2 in A
  constant _s_B1_1 in B
  constant _s_B1_0 in B
  relation p in A
  axiom {
    G
     (((((((!p(_s_A2_5) || p'(_s_A2_5)) && (!p'(_s_A2_5) || p(_s_A2_5))) &&
          ((!p(_s_A1_3) || p'(_s_A1_3)) && (!p'(_s_A1_3) || p(_s_A1_3))))
         ||
         (((!p(_s_A2_5) || p'(_s_A2_5)) && (!p'(_s_A2_5) || p(_s_A2_5))) &&
          ((!p(_s_A1_3) || p'(_s_A1_3)) && (!p'(_s_A1_3) || p(_s_A1_3)))))
        ||
        ((((!p(_s_A2_4) || p'(_s_A2_4)) && (!p'(_s_A2_4) || p(_s_A2_4))) &&
          ((!p(_s_A1_3) || p'(_s_A1_3)) && (!p'(_s_A1_3) || p(_s_A1_3))))
         ||
         (((!p(_s_A2_4) || p'(_s_A2_4)) && (!p'(_s_A2_4) || p(_s_A2_4))) &&
          ((!p(_s_A1_3) || p'(_s_A1_3)) && (!p'(_s_A1_3) || p(_s_A1_3))))))
       ||
       (((((!p(_s_A2_5) || p'(_s_A2_5)) && (!p'(_s_A2_5) || p(_s_A2_5))) &&
          ((!p(_s_A1_2) || p'(_s_A1_2)) && (!p'(_s_A1_2) || p(_s_A1_2))))
         ||
         (((!p(_s_A2_5) || p'(_s_A2_5)) && (!p'(_s_A2_5) || p(_s_A2_5))) &&
          ((!p(_s_A1_2) || p'(_s_A1_2)) && (!p'(_s_A1_2) || p(_s_A1_2)))))
        ||
        ((((!p(_s_A2_4) || p'(_s_A2_4)) && (!p'(_s_A2_4) || p(_s_A2_4))) &&
          ((!p(_s_A1_2) || p'(_s_A1_2)) && (!p'(_s_A1_2) || p(_s_A1_2))))
         ||
         (((!p(_s_A2_4) || p'(_s_A2_4)) && (!p'(_s_A2_4) || p(_s_A2_4))) &&
          ((!p(_s_A1_2) || p'(_s_A1_2)) && (!p'(_s_A1_2) || p(_s_A1_2)))))))
      ||
      ((((((!p(_s_A2_5) || p'(_s_A2_5)) && (!p'(_s_A2_5) || p(_s_A2_5))) &&
          ((!p(_s_A1_2) || p'(_s_A1_2)) && (!p'(_s_A1_2) || p(_s_A1_2))))
         ||
         (((!p(_s_A2_5) || p'(_s_A2_5)) && (!p'(_s_A2_5) || p(_s_A2_5))) &&
          ((!p(_s_A1_2) || p'(_s_A1_2)) && (!p'(_s_A1_2) || p(_s_A1_2)))))
        ||
        ((((!p(_s_A2_4) || p'(_s_A2_4)) && (!p'(_s_A2_4) || p(_s_A2_4))) &&
          ((!p(_s_A1_2) || p'(_s_A1_2)) && (!p'(_s_A1_2) || p(_s_A1_2))))
         ||
         (((!p(_s_A2_4) || p'(_s_A2_4)) && (!p'(_s_A2_4) || p(_s_A2_4))) &&
          ((!p(_s_A1_2) || p'(_s_A1_2)) && (!p'(_s_A1_2) || p(_s_A1_2))))))
       ||
       (((((!p(_s_A2_4) || p'(_s_A2_4)) && (!p'(_s_A2_4) || p(_s_A2_4))) &&
          ((!p(_s_A1_3) || p'(_s_A1_3)) && (!p'(_s_A1_3) || p(_s_A1_3))))
         ||
         (((!p(_s_A2_4) || p'(_s_A2_4)) && (!p'(_s_A2_4) || p(_s_A2_4))) &&
          ((!p(_s_A1_3) || p'(_s_A1_3)) && (!p'(_s_A1_3) || p(_s_A1_3)))))
        ||
        ((((!p(_s_A2_5) || p'(_s_A2_5)) && (!p'(_s_A2_5) || p(_s_A2_5))) &&
          ((!p(_s_A1_3) || p'(_s_A1_3)) && (!p'(_s_A1_3) || p(_s_A1_3))))
         ||
         (((!p(_s_A2_5) || p'(_s_A2_5)) && (!p'(_s_A2_5) || p(_s_A2_5))) &&
          ((!p(_s_A1_3) || p'(_s_A1_3)) && (!p'(_s_A1_3) || p(_s_A1_3)))))))) }
  axiom { false }
  axiom { true }
  check prop { false }
  assuming { true } using TFC[]

