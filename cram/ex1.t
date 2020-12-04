Tests the plain Semantics.
  $ cervino sem ex1.cervino
  cervino (C) 2020 ONERA (development version)
  sig Process {}
  sig index {}
  one sig zero in index {}
  one sig _M {
    var prev_index : index -> index,
    var prev_tc : index -> index,
    var list : index -> Process,
    var is_in_list : set Process,
    var last_list : set index,
  }
  fact { (!{}) }
  fact { ({}) }
  fact {
    always (some _s_index1: index | (some _s_Process1: Process |
     (((_s_index1 in _M.last_list &&
        (_s_Process1 !in _M.is_in_list && _s_index1->_s_Process1 in _M.list'))
       &&
       (((all _em0: index | (all _em1: Process |
         ((_em0 = _s_index1 && _em1 = _s_Process1) ||
          ((_em0->_em1 !in _M.list || _em0->_em1 in _M.list') &&
           (_em0->_em1 !in _M.list' || _em0->_em1 in _M.list)))))
         && (all _em0: Process |
         (_em0 = _s_Process1 ||
          ((_em0 !in _M.is_in_list || _em0 in _M.is_in_list') &&
           (_em0 !in _M.is_in_list' || _em0 in _M.is_in_list)))))
        &&
        ((all _em0: index | (all _em1: index |
         ((_em0->_em1 !in _M.prev_index || _em0->_em1 in _M.prev_index') &&
          (_em0->_em1 !in _M.prev_index' || _em0->_em1 in _M.prev_index))))
         && (all _em0: index | (all _em1: index |
         ((_em0->_em1 !in _M.prev_tc || _em0->_em1 in _M.prev_tc') &&
          (_em0->_em1 !in _M.prev_tc' || _em0->_em1 in _M.prev_tc)))))))
      ||
      ((zero->_s_Process1 in _M.list && (all i: index | (all i2: index |
        (all p: Process |
        (i->i2 !in _M.prev_index ||
         ((i->p !in _M.list || i2->p in _M.list') &&
          (i2->p !in _M.list' || i->p in _M.list)))))))
       &&
       ((all _em0: Process |
        (_em0 = _s_Process1 ||
         ((_em0 !in _M.is_in_list || _em0 in _M.is_in_list') &&
          (_em0 !in _M.is_in_list' || _em0 in _M.is_in_list))))
        &&
        ((all _em0: index | (all _em1: index |
         ((_em0->_em1 !in _M.prev_index || _em0->_em1 in _M.prev_index') &&
          (_em0->_em1 !in _M.prev_index' || _em0->_em1 in _M.prev_index))))
         && (all _em0: index | (all _em1: index |
         ((_em0->_em1 !in _M.prev_tc || _em0->_em1 in _M.prev_tc') &&
          (_em0->_em1 !in _M.prev_tc' || _em0->_em1 in _M.prev_tc)))))))))) }
  fact /* assuming */ { ({}) }
  check sem { (!{}) }
