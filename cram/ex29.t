Tests keeping the event axiom "folded"...
  $ cervino -c prop ex29.cervino
  cervino (C) 2020 ONERA (development version)
  sort A
  
  relation p in A
  axiom {
    G (some _s_A1: A | ((!p(_s_A1) || p'(_s_A1)) && (!p'(_s_A1) || p(_s_A1))))
    }
  axiom { false }
  axiom { true }
  check prop { false }
  assuming { true } using TFC[]
...vs unfolded on two constants per existential bound variable under G
  $ cervino -cu prop ex29.cervino
  cervino (C) 2020 ONERA (development version)
  sort A
  constant _s_A1_0 in A
  constant _s_A1_1 in A
  relation p in A
  axiom {
    G
     (((!p(_s_A1_0) || p'(_s_A1_0)) && (!p'(_s_A1_0) || p(_s_A1_0))) ||
      ((!p(_s_A1_1) || p'(_s_A1_1)) && (!p'(_s_A1_1) || p(_s_A1_1)))) }
  axiom { false }
  axiom { true }
  check prop { false }
  assuming { true } using TFC[]

