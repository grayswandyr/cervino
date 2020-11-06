Tests the TTC Transformation.
  $ cervino ttc ex7.cervino
  cervino (C) 2020 ONERA (development version)
  sig Id {}
  one sig imax in Id {}
  one sig _sk__tcPx_0 in Id {}
  one sig _sk__tcPy_1 in Id {}
  one sig _M {
    var succ : Id -> Id,
    var succ_tc : Id -> Id,
    var _eq_Id : Id -> Id,
  }
  fact {
    always
     (((((imax->imax !in _M.succ || imax->imax in _M.succ') &&
         (imax->imax !in _M.succ' || imax->imax in _M.succ))
        &&
        (((imax->_sk__tcPx_0 !in _M.succ || imax->_sk__tcPx_0 in _M.succ') &&
          (imax->_sk__tcPx_0 !in _M.succ' || imax->_sk__tcPx_0 in _M.succ))
         &&
         ((imax->_sk__tcPy_1 !in _M.succ || imax->_sk__tcPy_1 in _M.succ') &&
          (imax->_sk__tcPy_1 !in _M.succ' || imax->_sk__tcPy_1 in _M.succ))))
       &&
       ((((_sk__tcPx_0->imax !in _M.succ || _sk__tcPx_0->imax in _M.succ') &&
          (_sk__tcPx_0->imax !in _M.succ' || _sk__tcPx_0->imax in _M.succ))
         &&
         (((_sk__tcPx_0->_sk__tcPx_0 !in _M.succ ||
            _sk__tcPx_0->_sk__tcPx_0 in _M.succ')
           &&
           (_sk__tcPx_0->_sk__tcPx_0 !in _M.succ' ||
            _sk__tcPx_0->_sk__tcPx_0 in _M.succ))
          &&
          ((_sk__tcPx_0->_sk__tcPy_1 !in _M.succ ||
            _sk__tcPx_0->_sk__tcPy_1 in _M.succ')
           &&
           (_sk__tcPx_0->_sk__tcPy_1 !in _M.succ' ||
            _sk__tcPx_0->_sk__tcPy_1 in _M.succ))))
        &&
        (((_sk__tcPy_1->imax !in _M.succ || _sk__tcPy_1->imax in _M.succ') &&
          (_sk__tcPy_1->imax !in _M.succ' || _sk__tcPy_1->imax in _M.succ))
         &&
         (((_sk__tcPy_1->_sk__tcPx_0 !in _M.succ ||
            _sk__tcPy_1->_sk__tcPx_0 in _M.succ')
           &&
           (_sk__tcPy_1->_sk__tcPx_0 !in _M.succ' ||
            _sk__tcPy_1->_sk__tcPx_0 in _M.succ))
          &&
          ((_sk__tcPy_1->_sk__tcPy_1 !in _M.succ ||
            _sk__tcPy_1->_sk__tcPy_1 in _M.succ')
           &&
           (_sk__tcPy_1->_sk__tcPy_1 !in _M.succ' ||
            _sk__tcPy_1->_sk__tcPy_1 in _M.succ))))))
      &&
      (((((imax->imax !in _M.succ_tc || imax->imax in _M.succ_tc') &&
          (imax->imax !in _M.succ_tc' || imax->imax in _M.succ_tc))
         &&
         (((imax->_sk__tcPx_0 !in _M.succ_tc ||
            imax->_sk__tcPx_0 in _M.succ_tc')
           &&
           (imax->_sk__tcPx_0 !in _M.succ_tc' ||
            imax->_sk__tcPx_0 in _M.succ_tc))
          &&
          ((imax->_sk__tcPy_1 !in _M.succ_tc ||
            imax->_sk__tcPy_1 in _M.succ_tc')
           &&
           (imax->_sk__tcPy_1 !in _M.succ_tc' ||
            imax->_sk__tcPy_1 in _M.succ_tc))))
        &&
        ((((_sk__tcPx_0->imax !in _M.succ_tc ||
            _sk__tcPx_0->imax in _M.succ_tc')
           &&
           (_sk__tcPx_0->imax !in _M.succ_tc' ||
            _sk__tcPx_0->imax in _M.succ_tc))
          &&
          (((_sk__tcPx_0->_sk__tcPx_0 !in _M.succ_tc ||
             _sk__tcPx_0->_sk__tcPx_0 in _M.succ_tc')
            &&
            (_sk__tcPx_0->_sk__tcPx_0 !in _M.succ_tc' ||
             _sk__tcPx_0->_sk__tcPx_0 in _M.succ_tc))
           &&
           ((_sk__tcPx_0->_sk__tcPy_1 !in _M.succ_tc ||
             _sk__tcPx_0->_sk__tcPy_1 in _M.succ_tc')
            &&
            (_sk__tcPx_0->_sk__tcPy_1 !in _M.succ_tc' ||
             _sk__tcPx_0->_sk__tcPy_1 in _M.succ_tc))))
         &&
         (((_sk__tcPy_1->imax !in _M.succ_tc ||
            _sk__tcPy_1->imax in _M.succ_tc')
           &&
           (_sk__tcPy_1->imax !in _M.succ_tc' ||
            _sk__tcPy_1->imax in _M.succ_tc))
          &&
          (((_sk__tcPy_1->_sk__tcPx_0 !in _M.succ_tc ||
             _sk__tcPy_1->_sk__tcPx_0 in _M.succ_tc')
            &&
            (_sk__tcPy_1->_sk__tcPx_0 !in _M.succ_tc' ||
             _sk__tcPy_1->_sk__tcPx_0 in _M.succ_tc))
           &&
           ((_sk__tcPy_1->_sk__tcPy_1 !in _M.succ_tc ||
             _sk__tcPy_1->_sk__tcPy_1 in _M.succ_tc')
            &&
            (_sk__tcPy_1->_sk__tcPy_1 !in _M.succ_tc' ||
             _sk__tcPy_1->_sk__tcPy_1 in _M.succ_tc))))))
       &&
       ((((imax->imax !in _M._eq_Id || imax->imax in _M._eq_Id') &&
          (imax->imax !in _M._eq_Id' || imax->imax in _M._eq_Id))
         &&
         (((imax->_sk__tcPx_0 !in _M._eq_Id || imax->_sk__tcPx_0 in _M._eq_Id')
           &&
           (imax->_sk__tcPx_0 !in _M._eq_Id' || imax->_sk__tcPx_0 in _M._eq_Id))
          &&
          ((imax->_sk__tcPy_1 !in _M._eq_Id || imax->_sk__tcPy_1 in _M._eq_Id')
           &&
           (imax->_sk__tcPy_1 !in _M._eq_Id' || imax->_sk__tcPy_1 in _M._eq_Id))))
        &&
        ((((_sk__tcPx_0->imax !in _M._eq_Id || _sk__tcPx_0->imax in _M._eq_Id')
           &&
           (_sk__tcPx_0->imax !in _M._eq_Id' || _sk__tcPx_0->imax in _M._eq_Id))
          &&
          (((_sk__tcPx_0->_sk__tcPx_0 !in _M._eq_Id ||
             _sk__tcPx_0->_sk__tcPx_0 in _M._eq_Id')
            &&
            (_sk__tcPx_0->_sk__tcPx_0 !in _M._eq_Id' ||
             _sk__tcPx_0->_sk__tcPx_0 in _M._eq_Id))
           &&
           ((_sk__tcPx_0->_sk__tcPy_1 !in _M._eq_Id ||
             _sk__tcPx_0->_sk__tcPy_1 in _M._eq_Id')
            &&
            (_sk__tcPx_0->_sk__tcPy_1 !in _M._eq_Id' ||
             _sk__tcPx_0->_sk__tcPy_1 in _M._eq_Id))))
         &&
         (((_sk__tcPy_1->imax !in _M._eq_Id || _sk__tcPy_1->imax in _M._eq_Id')
           &&
           (_sk__tcPy_1->imax !in _M._eq_Id' || _sk__tcPy_1->imax in _M._eq_Id))
          &&
          (((_sk__tcPy_1->_sk__tcPx_0 !in _M._eq_Id ||
             _sk__tcPy_1->_sk__tcPx_0 in _M._eq_Id')
            &&
            (_sk__tcPy_1->_sk__tcPx_0 !in _M._eq_Id' ||
             _sk__tcPy_1->_sk__tcPx_0 in _M._eq_Id))
           &&
           ((_sk__tcPy_1->_sk__tcPy_1 !in _M._eq_Id ||
             _sk__tcPy_1->_sk__tcPy_1 in _M._eq_Id')
            &&
            (_sk__tcPy_1->_sk__tcPy_1 !in _M._eq_Id' ||
             _sk__tcPy_1->_sk__tcPy_1 in _M._eq_Id)))))))) }
  fact {
    ((_sk__tcPx_0->_sk__tcPy_1 in _M.succ &&
      eventually
       (_sk__tcPx_0->imax in _M.succ && always _sk__tcPy_1->imax !in _M.succ))
     ||
     (((imax->imax !in _M.succ_tc ||
        always (imax->imax !in _M.succ || eventually imax->imax in _M.succ))
       &&
       ((imax->_sk__tcPx_0 !in _M.succ_tc ||
         always
          (imax->imax !in _M.succ || eventually _sk__tcPx_0->imax in _M.succ))
        &&
        (imax->_sk__tcPy_1 !in _M.succ_tc ||
         always
          (imax->imax !in _M.succ || eventually _sk__tcPy_1->imax in _M.succ))))
      &&
      (((_sk__tcPx_0->imax !in _M.succ_tc ||
         always
          (_sk__tcPx_0->imax !in _M.succ || eventually imax->imax in _M.succ))
        &&
        ((_sk__tcPx_0->_sk__tcPx_0 !in _M.succ_tc ||
          always
           (_sk__tcPx_0->imax !in _M.succ ||
            eventually _sk__tcPx_0->imax in _M.succ))
         &&
         (_sk__tcPx_0->_sk__tcPy_1 !in _M.succ_tc ||
          always
           (_sk__tcPx_0->imax !in _M.succ ||
            eventually _sk__tcPy_1->imax in _M.succ))))
       &&
       ((_sk__tcPy_1->imax !in _M.succ_tc ||
         always
          (_sk__tcPy_1->imax !in _M.succ || eventually imax->imax in _M.succ))
        &&
        ((_sk__tcPy_1->_sk__tcPx_0 !in _M.succ_tc ||
          always
           (_sk__tcPy_1->imax !in _M.succ ||
            eventually _sk__tcPx_0->imax in _M.succ))
         &&
         (_sk__tcPy_1->_sk__tcPy_1 !in _M.succ_tc ||
          always
           (_sk__tcPy_1->imax !in _M.succ ||
            eventually _sk__tcPy_1->imax in _M.succ))))))) }
  fact { imax->imax in _M._eq_Id }
  fact {
    always (all _x: Id | (all _y: Id |
     (_x->_y !in _M._eq_Id ||
      ((all _e0: Id |
       ((_e0->_x !in _M.succ || _e0->_y in _M.succ) &&
        (_e0->_y !in _M.succ || _e0->_x in _M.succ)))
       &&
       ((all _e0: Id |
        ((_x->_e0 !in _M.succ || _y->_e0 in _M.succ) &&
         (_y->_e0 !in _M.succ || _x->_e0 in _M.succ)))
        &&
        ((all _e0: Id |
         ((_e0->_x !in _M.succ_tc || _e0->_y in _M.succ_tc) &&
          (_e0->_y !in _M.succ_tc || _e0->_x in _M.succ_tc)))
         && (all _e0: Id |
         ((_x->_e0 !in _M.succ_tc || _y->_e0 in _M.succ_tc) &&
          (_y->_e0 !in _M.succ_tc || _x->_e0 in _M.succ_tc))))))))) }
  fact {
    always (all _x: Id | (all _y: Id | (all _z: Id |
     (_x->_x in _M._eq_Id &&
      ((_x->_y !in _M._eq_Id || _y->_x in _M._eq_Id) &&
       ((_x->_y !in _M._eq_Id || _y->_z !in _M._eq_Id) || _x->_z in _M._eq_Id))))))
    }
  fact /* assuming */ { no none }
  check ttc { no none }
