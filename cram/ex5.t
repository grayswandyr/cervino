Tests the TTC Transformation.
  $ cervino ttc ex5.cervino
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
    var _eq_index : index -> index,
  }
  fact {
    always (some _s_index1: index | (some _s_Process1: Process |
     (_s_index1->_s_Process1 in _M.list' &&
      ((((zero->_s_index1 in _M._eq_index && cst->_s_Process1 in _M._eq_Process) ||
         ((zero->cst !in _M.list || zero->cst in _M.list') &&
          (zero->cst !in _M.list' || zero->cst in _M.list)))
        &&
        (((_sk__tcPx_0->_s_index1 in _M._eq_index && cst->_s_Process1 in _M._eq_Process) ||
          ((_sk__tcPx_0->cst !in _M.list || _sk__tcPx_0->cst in _M.list') &&
           (_sk__tcPx_0->cst !in _M.list' || _sk__tcPx_0->cst in _M.list)))
         &&
         ((_sk__tcPy_1->_s_index1 in _M._eq_index && cst->_s_Process1 in _M._eq_Process) ||
          ((_sk__tcPy_1->cst !in _M.list || _sk__tcPy_1->cst in _M.list') &&
           (_sk__tcPy_1->cst !in _M.list' || _sk__tcPy_1->cst in _M.list)))))
       &&
       (((((zero->zero !in _M.prev_index || zero->zero in _M.prev_index') &&
           (zero->zero !in _M.prev_index' || zero->zero in _M.prev_index))
          &&
          (((zero->_sk__tcPx_0 !in _M.prev_index ||
             zero->_sk__tcPx_0 in _M.prev_index')
            &&
            (zero->_sk__tcPx_0 !in _M.prev_index' ||
             zero->_sk__tcPx_0 in _M.prev_index))
           &&
           ((zero->_sk__tcPy_1 !in _M.prev_index ||
             zero->_sk__tcPy_1 in _M.prev_index')
            &&
            (zero->_sk__tcPy_1 !in _M.prev_index' ||
             zero->_sk__tcPy_1 in _M.prev_index))))
         &&
         ((((_sk__tcPx_0->zero !in _M.prev_index ||
             _sk__tcPx_0->zero in _M.prev_index')
            &&
            (_sk__tcPx_0->zero !in _M.prev_index' ||
             _sk__tcPx_0->zero in _M.prev_index))
           &&
           (((_sk__tcPx_0->_sk__tcPx_0 !in _M.prev_index ||
              _sk__tcPx_0->_sk__tcPx_0 in _M.prev_index')
             &&
             (_sk__tcPx_0->_sk__tcPx_0 !in _M.prev_index' ||
              _sk__tcPx_0->_sk__tcPx_0 in _M.prev_index))
            &&
            ((_sk__tcPx_0->_sk__tcPy_1 !in _M.prev_index ||
              _sk__tcPx_0->_sk__tcPy_1 in _M.prev_index')
             &&
             (_sk__tcPx_0->_sk__tcPy_1 !in _M.prev_index' ||
              _sk__tcPx_0->_sk__tcPy_1 in _M.prev_index))))
          &&
          (((_sk__tcPy_1->zero !in _M.prev_index ||
             _sk__tcPy_1->zero in _M.prev_index')
            &&
            (_sk__tcPy_1->zero !in _M.prev_index' ||
             _sk__tcPy_1->zero in _M.prev_index))
           &&
           (((_sk__tcPy_1->_sk__tcPx_0 !in _M.prev_index ||
              _sk__tcPy_1->_sk__tcPx_0 in _M.prev_index')
             &&
             (_sk__tcPy_1->_sk__tcPx_0 !in _M.prev_index' ||
              _sk__tcPy_1->_sk__tcPx_0 in _M.prev_index))
            &&
            ((_sk__tcPy_1->_sk__tcPy_1 !in _M.prev_index ||
              _sk__tcPy_1->_sk__tcPy_1 in _M.prev_index')
             &&
             (_sk__tcPy_1->_sk__tcPy_1 !in _M.prev_index' ||
              _sk__tcPy_1->_sk__tcPy_1 in _M.prev_index))))))
        &&
        ((((zero->zero !in _M.prev_tc || zero->zero in _M.prev_tc') &&
           (zero->zero !in _M.prev_tc' || zero->zero in _M.prev_tc))
          &&
          (((zero->_sk__tcPx_0 !in _M.prev_tc ||
             zero->_sk__tcPx_0 in _M.prev_tc')
            &&
            (zero->_sk__tcPx_0 !in _M.prev_tc' ||
             zero->_sk__tcPx_0 in _M.prev_tc))
           &&
           ((zero->_sk__tcPy_1 !in _M.prev_tc ||
             zero->_sk__tcPy_1 in _M.prev_tc')
            &&
            (zero->_sk__tcPy_1 !in _M.prev_tc' ||
             zero->_sk__tcPy_1 in _M.prev_tc))))
         &&
         ((((_sk__tcPx_0->zero !in _M.prev_tc ||
             _sk__tcPx_0->zero in _M.prev_tc')
            &&
            (_sk__tcPx_0->zero !in _M.prev_tc' ||
             _sk__tcPx_0->zero in _M.prev_tc))
           &&
           (((_sk__tcPx_0->_sk__tcPx_0 !in _M.prev_tc ||
              _sk__tcPx_0->_sk__tcPx_0 in _M.prev_tc')
             &&
             (_sk__tcPx_0->_sk__tcPx_0 !in _M.prev_tc' ||
              _sk__tcPx_0->_sk__tcPx_0 in _M.prev_tc))
            &&
            ((_sk__tcPx_0->_sk__tcPy_1 !in _M.prev_tc ||
              _sk__tcPx_0->_sk__tcPy_1 in _M.prev_tc')
             &&
             (_sk__tcPx_0->_sk__tcPy_1 !in _M.prev_tc' ||
              _sk__tcPx_0->_sk__tcPy_1 in _M.prev_tc))))
          &&
          (((_sk__tcPy_1->zero !in _M.prev_tc ||
             _sk__tcPy_1->zero in _M.prev_tc')
            &&
            (_sk__tcPy_1->zero !in _M.prev_tc' ||
             _sk__tcPy_1->zero in _M.prev_tc))
           &&
           (((_sk__tcPy_1->_sk__tcPx_0 !in _M.prev_tc ||
              _sk__tcPy_1->_sk__tcPx_0 in _M.prev_tc')
             &&
             (_sk__tcPy_1->_sk__tcPx_0 !in _M.prev_tc' ||
              _sk__tcPy_1->_sk__tcPx_0 in _M.prev_tc))
            &&
            ((_sk__tcPy_1->_sk__tcPy_1 !in _M.prev_tc ||
              _sk__tcPy_1->_sk__tcPy_1 in _M.prev_tc')
             &&
             (_sk__tcPy_1->_sk__tcPy_1 !in _M.prev_tc' ||
              _sk__tcPy_1->_sk__tcPy_1 in _M.prev_tc))))))))))) }
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
    (((all _e0: index |
     ((_e0->_x !in _M.list || _e0->_y in _M.list) &&
      (_e0->_y !in _M.list || _e0->_x in _M.list))))))) }
  fact {
    always (all _x: index | (all _y: index |
     (_x->_y !in _M._eq_index ||
      ((all _e0: index |
       ((_e0->_x !in _M.prev_index || _e0->_y in _M.prev_index) &&
        (_e0->_y !in _M.prev_index || _e0->_x in _M.prev_index)))
       &&
       ((all _e0: index |
        ((_x->_e0 !in _M.prev_index || _y->_e0 in _M.prev_index) &&
         (_y->_e0 !in _M.prev_index || _x->_e0 in _M.prev_index)))
        &&
        ((all _e0: index |
         ((_e0->_x !in _M.prev_tc || _e0->_y in _M.prev_tc) &&
          (_e0->_y !in _M.prev_tc || _e0->_x in _M.prev_tc)))
         &&
        ((all _e0: index |
         ((_x->_e0 !in _M.prev_tc || _y->_e0 in _M.prev_tc) &&
          (_y->_e0 !in _M.prev_tc || _x->_e0 in _M.prev_tc)))
         && (all _e0: Process |
         ((_x->_e0 !in _M.list || _y->_e0 in _M.list) &&
          (_y->_e0 !in _M.list || _x->_e0 in _M.list)))))))))) }
  fact {
    always (all _x: Process | (all _y: Process | (all _z: Process |
     (_x->_x in _M._eq_Process &&
      ((_x->_y !in _M._eq_Process || _y->_x in _M._eq_Process) &&
       ((_x->_y !in _M._eq_Process || _y->_z !in _M._eq_Process) || _x->_z in _M._eq_Process))))))
    }
  fact {
    always (all _x: index | (all _y: index | (all _z: index |
     (_x->_x in _M._eq_index &&
      ((_x->_y !in _M._eq_index || _y->_x in _M._eq_index) &&
       ((_x->_y !in _M._eq_index || _y->_z !in _M._eq_index) || _x->_z in _M._eq_index))))))
    }
  fact /* assuming */ { no none }
  check ttc { no none }

