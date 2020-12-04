Tests the TTC Transformation.
  $ cervino tfc ex3.cervino
  cervino (C) 2020 ONERA (development version)
  sig Process {}
  sig index {}
  one sig zero in index {}
  one sig cst in Process {}
  one sig _M {
    var prev_index : index -> index,
    var prev_tc : index -> index,
    var list : index -> Process,
  }
  fact {
    always
     (((some x: Process | zero->x in _M.list) || (all x: Process |
       zero->x !in _M.list'))
      &&
      (((zero->zero !in _M.prev_index || zero->zero in _M.prev_index') &&
        (zero->zero !in _M.prev_index' || zero->zero in _M.prev_index))
       &&
       (((zero->zero !in _M.prev_tc || zero->zero in _M.prev_tc') &&
         (zero->zero !in _M.prev_tc' || zero->zero in _M.prev_tc))
        &&
        ((zero->cst !in _M.list || zero->cst in _M.list') &&
         (zero->cst !in _M.list' || zero->cst in _M.list))))) }
  fact { (!{}) }
  fact { ({}) }
  fact /* assuming */ { ({}) }
  check tfc { (!{}) }
