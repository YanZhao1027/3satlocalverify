import ConnectedCRT
set_option maxRecDepth 8192
set_option maxHeartbeats 0

theorem connected_crt_exact : ConnectedCRT.reconstructedSAT = 116 := by decide
theorem connected_crt_mod7 : ((ConnectedCRT.result 7).1.take 6).map ZMod.val = [4,1,6,0,0,0] := by decide
theorem connected_walsh_zero : ConnectedCRT.satWalsh 0 = 116 := by decide
