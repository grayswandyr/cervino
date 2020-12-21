Tests folding constants in instantiation
  $ cervino ttc ex26.cervino
  cervino (C) 2020 ONERA (development version)
  sig A {}
  sig B {}
  one sig c extends A {}
  one sig d extends A {}
  one sig e extends B {}
  one sig _M {
    var p : set A,
  }
  fact { always (!{}) }
  fact { (!{}) }
  fact { ({}) }
  fact { (c in _M.p' || c in _M.p) }
  fact { (eventually c in _M.p && eventually d in _M.p) }
  fact { eventually c in _M.p }
  fact { ({}) }
  fact /* assuming */ { ({}) }
  check ttc { (!{}) }

