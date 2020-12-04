Tests the TEA Transformation.
  $ cervino tea ex4.cervino
  cervino (C) 2020 ONERA (development version)
  sig Process {}
  sig index {}
  
  one sig _M {
    var _E_s_index1 : set index,
    var _E_s_Process1 : set Process,
    var list : index -> Process,
  }
  fact {
    always
     ((all _eax: index | (all _eay: index |
      ((_eax !in _M._E_s_index1 || _eay !in _M._E_s_index1) || _eax = _eay)))
      && (all _eax: Process | (all _eay: Process |
      ((_eax !in _M._E_s_Process1 || _eay !in _M._E_s_Process1) || _eax = _eay))))
    }
  fact {
    always (all _s_index1: index | (all _s_Process1: Process |
     ((_s_index1->_s_Process1 in _M.list' ||
       (_s_index1 !in _M._E_s_index1 || _s_Process1 !in _M._E_s_Process1))
      && (all _em0: index | (all _em1: Process |
      ((_em0 in _M._E_s_index1 && _em1 in _M._E_s_Process1) ||
       ((_em0->_em1 !in _M.list || _em0->_em1 in _M.list') &&
        (_em0->_em1 !in _M.list' || _em0->_em1 in _M.list)))))))) }
  fact { (!{}) }
  fact { ({}) }
  fact /* assuming */ { ({}) }
  check tea { (!{}) }
