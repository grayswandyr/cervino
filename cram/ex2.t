Tests the TTC Transformation.
  $ cervino ttc ex2.cervino
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
  }
  fact { (!{}) }
  fact { ({}) }
  fact {
    always
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
      (((((zero->zero !in _M.prev_tc || zero->zero in _M.prev_tc') &&
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
             _sk__tcPy_1->_sk__tcPy_1 in _M.prev_tc))))))
       &&
       (((zero->cst !in _M.list || zero->cst in _M.list') &&
         (zero->cst !in _M.list' || zero->cst in _M.list))
        &&
        (((_sk__tcPx_0->cst !in _M.list || _sk__tcPx_0->cst in _M.list') &&
          (_sk__tcPx_0->cst !in _M.list' || _sk__tcPx_0->cst in _M.list))
         &&
         ((_sk__tcPy_1->cst !in _M.list || _sk__tcPy_1->cst in _M.list') &&
          (_sk__tcPy_1->cst !in _M.list' || _sk__tcPy_1->cst in _M.list)))))) }
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
  fact /* assuming */ { ({}) }
  check ttc { (!{}) }
