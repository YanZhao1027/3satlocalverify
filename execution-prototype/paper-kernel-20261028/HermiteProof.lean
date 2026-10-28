import HermiteCRT
set_option maxRecDepth 8192
set_option maxHeartbeats 0

/-- Kernel checks the original source Hermite jets for one real connected 3SAT. -/
theorem connected_order2_mod7 : ((HermiteCRT.run 7).1.take 6).map ZMod.val =
    [4,1,6,0,0,0] := by decide
theorem connected_order2_mod11 : ((HermiteCRT.run 11).1.take 6).map ZMod.val =
    [6,10,9,0,0,0] := by decide
theorem connected_order2_mod13 : ((HermiteCRT.run 13).1.take 6).map ZMod.val =
    [12,3,7,0,0,0] := by decide

theorem connected_order3_mod7 : ((HermiteHigher.run3 7).1.take 6).map ZMod.val =
    [4,1,6,0,0,0] := by decide
theorem connected_order3_mod11 : ((HermiteHigher.run3 11).1.take 6).map ZMod.val =
    [6,10,9,0,0,0] := by decide
theorem connected_order3_mod13 : ((HermiteHigher.run3 13).1.take 6).map ZMod.val =
    [12,3,7,0,0,0] := by decide

theorem source_hermite_cost_order2 :
    (HermiteCRT.run 7).2 + (HermiteCRT.run 11).2 + (HermiteCRT.run 13).2 = 2919 := by decide
theorem source_hermite_cost_order3 :
    (HermiteHigher.run3 7).2 + (HermiteHigher.run3 11).2 +
      (HermiteHigher.run3 13).2 = 2201 := by decide
