Tests the TTC Transformation.
  $ cervino ttc ex6.cervino
  cervino (C) 2020 ONERA (development version)
  sig Process {}
  sig index {}
  one sig zero in index {}
  one sig cst in Process {}
  one sig _sk__tcPx_0 in index {}
  one sig _sk__tcPy_1 in index {}
  one sig _M {
    var prev_index : index -> index,
    var prev_tc : index -> index,
    var list : index -> Process,
    var _eq_Process : Process -> Process,
  }
  fact {
    always (some _s_Process1: Process |
     (_s_Process1->_s_Process1 in _M._eq_Process &&
      ((cst->cst !in _M._eq_Process || cst->cst in _M._eq_Process') &&
       (cst->cst !in _M._eq_Process' || cst->cst in _M._eq_Process)))) }
  fact {
    ((_sk__tcPx_0->_sk__tcPy_1 in _M.prev_index &&
      eventually
       (_sk__tcPx_0->cst in _M.list && always _sk__tcPy_1->cst !in _M.list))
     ||
     (((zero->zero !in _M.prev_tc ||
        always (zero->cst !in _M.list || eventually zero->cst in _M.list))
       &&
       ((zero->_sk__tcPx_0 !in _M.prev_tc ||
         always
          (zero->cst !in _M.list || eventually _sk__tcPx_0->cst in _M.list))
        &&
        (zero->_sk__tcPy_1 !in _M.prev_tc ||
         always
          (zero->cst !in _M.list || eventually _sk__tcPy_1->cst in _M.list))))
      &&
      (((_sk__tcPx_0->zero !in _M.prev_tc ||
         always
          (_sk__tcPx_0->cst !in _M.list || eventually zero->cst in _M.list))
        &&
        ((_sk__tcPx_0->_sk__tcPx_0 !in _M.prev_tc ||
          always
           (_sk__tcPx_0->cst !in _M.list ||
            eventually _sk__tcPx_0->cst in _M.list))
         &&
         (_sk__tcPx_0->_sk__tcPy_1 !in _M.prev_tc ||
          always
           (_sk__tcPx_0->cst !in _M.list ||
            eventually _sk__tcPy_1->cst in _M.list))))
       &&
       ((_sk__tcPy_1->zero !in _M.prev_tc ||
         always
          (_sk__tcPy_1->cst !in _M.list || eventually zero->cst in _M.list))
        &&
        ((_sk__tcPy_1->_sk__tcPx_0 !in _M.prev_tc ||
          always
           (_sk__tcPy_1->cst !in _M.list ||
            eventually _sk__tcPx_0->cst in _M.list))
         &&
         (_sk__tcPy_1->_sk__tcPy_1 !in _M.prev_tc ||
          always
           (_sk__tcPy_1->cst !in _M.list ||
            eventually _sk__tcPy_1->cst in _M.list))))))) }
  fact {
    always (all _x: Process | (all _y: Process |
     (_x->_y !in _M._eq_Process || (all _e0: index |
      ((_e0->_x !in _M.list || _e0->_y in _M.list) &&
       (_e0->_y !in _M.list || _e0->_x in _M.list)))))) }
  fact {
    always (all _x: Process | (all _y: Process | (all _z: Process |
     (_x->_x in _M._eq_Process &&
      ((_x->_y !in _M._eq_Process || _y->_x in _M._eq_Process) &&
       ((_x->_y !in _M._eq_Process || _y->_z !in _M._eq_Process) ||
        _x->_z in _M._eq_Process)))))) }
  fact /* assuming */ { no none }
  check ttc { no none }
