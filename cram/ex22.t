Tests well formedness criteria.
  $ cervino prop ex22.cervino
  cervino (C) 2020 ONERA (development version)
  sig Id {}
  
  one sig _M {
    var _E_s_Id1 : set Id,
    var _E_s_Id2 : set Id,
    var succ : Id -> Id,
  }
  fact {
    always (all _s_Id1: Id | (all _s_Id2: Id |
     ((all z: Id | (_s_Id1->z !in _M.succ || _s_Id1 !in _M._E_s_Id1)) &&
      (all _em0: Id | (all _em1: Id |
      ((_em0->_em1 !in _M.succ || _em0->_em1 in _M.succ') &&
       (_em0->_em1 !in _M.succ' || _em0->_em1 in _M.succ))))))) }
  fact {
    always (all _eax: Id | (all _eay: Id |
     (((_eax !in _M._E_s_Id2 || _eay !in _M._E_s_Id2) || _eax = _eay) &&
      ((_eax !in _M._E_s_Id1 || _eay !in _M._E_s_Id1) || _eax = _eay)))) }
  fact /* assuming */ { ({}) }
  check prop { ({}) }
