import PlattAssemblyKernel
import PlattCertificates.Count131072.C030704
import PlattCertificates.Count131072.C030705
import PlattCertificates.Count131072.C030706
import PlattCertificates.Count131072.C030707
import PlattCertificates.Count131072.C030708
import PlattCertificates.Count131072.C030709
import PlattCertificates.Count131072.C030710
import PlattCertificates.Count131072.C030711
import PlattCertificates.Count131072.C030712
import PlattCertificates.Count131072.C030713
import PlattCertificates.Count131072.C030714
import PlattCertificates.Count131072.C030715
import PlattCertificates.Count131072.C030716
import PlattCertificates.Count131072.C030717
import PlattCertificates.Count131072.C030718
import PlattCertificates.Count131072.C030719
import PlattCertificates.Count131072.C030720
import PlattCertificates.Count131072.C030721
import PlattCertificates.Count131072.C030722
import PlattCertificates.Count131072.C030723
import PlattCertificates.Count131072.C030724
import PlattCertificates.Count131072.C030725
import PlattCertificates.Count131072.C030726
import PlattCertificates.Count131072.C030727
import PlattCertificates.Count131072.C030728
import PlattCertificates.Count131072.C030729
import PlattCertificates.Count131072.C030730
import PlattCertificates.Count131072.C030731
import PlattCertificates.Count131072.C030732
import PlattCertificates.Count131072.C030733
import PlattCertificates.Count131072.C030734
import PlattCertificates.Count131072.C030735
namespace ChenEffective.PlattWindow.Assembly.Prefix.S4.B000022
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts30704 : List PrefixCut := [⟨60,195433856,195433965⟩,
⟨128,415808701,415808936⟩]
theorem checked30704 : checkPrefixCuts (2^48) 4028366849 9 Manual.Count131072.C030704.packed 128 cuts30704 = true := by
 decide +kernel
def pointBounds30704 : List (Nat × Nat × Nat) := [(4028428288,105523205538984,105523589026240)]
theorem point_links_checked30704 : (cuts30704.take 1).map (fun c => (4028366849-1+2*2^9*c.k,105523010105128+c.lower,105523393592275+c.upper)) = pointBounds30704 := by
 decide +kernel
def cuts30705 : List PrefixCut := [⟨55,178938203,178938302⟩,
⟨128,410065885,410066115⟩]
theorem checked30705 : checkPrefixCuts (2^48) 4028497921 9 Manual.Count131072.C030705.packed 128 cuts30705 = true := by
 decide +kernel
def pointBounds30705 : List (Nat × Nat × Nat) := [(4028554240,105523604852032,105523988339513)]
theorem point_links_checked30705 : (cuts30705.take 1).map (fun c => (4028497921-1+2*2^9*c.k,105523425913829+c.lower,105523809401211+c.upper)) = pointBounds30705 := by
 decide +kernel
def cuts30706 : List PrefixCut := [⟨50,162862806,162862897⟩,
⟨128,413336251,413336485⟩]
theorem checked30706 : checkPrefixCuts (2^48) 4028628993 9 Manual.Count131072.C030706.packed 128 cuts30706 = true := by
 decide +kernel
def pointBounds30706 : List (Nat × Nat × Nat) := [(4028680192,105523998842520,105524382330223)]
theorem point_links_checked30706 : (cuts30706.take 1).map (fun c => (4028628993-1+2*2^9*c.k,105523835979714+c.lower,105524219467326+c.upper)) = pointBounds30706 := by
 decide +kernel
def cuts30707 : List PrefixCut := [⟨45,143784209,143784290⟩,
⟨128,415069398,415069625⟩]
theorem checked30707 : checkPrefixCuts (2^48) 4028760065 9 Manual.Count131072.C030707.packed 128 cuts30707 = true := by
 decide +kernel
def pointBounds30707 : List (Nat × Nat × Nat) := [(4028806144,105524393100174,105524776588101)]
theorem point_links_checked30707 : (cuts30707.take 1).map (fun c => (4028760065-1+2*2^9*c.k,105524249315965+c.lower,105524632803811+c.upper)) = pointBounds30707 := by
 decide +kernel
def cuts30708 : List PrefixCut := [⟨40,127501363,127501437⟩,
⟨128,418060006,418060244⟩]
theorem checked30708 : checkPrefixCuts (2^48) 4028891137 9 Manual.Count131072.C030708.packed 128 cuts30708 = true := by
 decide +kernel
def pointBounds30708 : List (Nat × Nat × Nat) := [(4028932096,105524791886726,105525175374873)]
theorem point_links_checked30708 : (cuts30708.take 1).map (fun c => (4028891137-1+2*2^9*c.k,105524664385363+c.lower,105525047873436+c.upper)) = pointBounds30708 := by
 decide +kernel
def cuts30709 : List PrefixCut := [⟨35,112407189,112407254⟩,
⟨128,415601308,415601546⟩]
theorem checked30709 : checkPrefixCuts (2^48) 4029022209 9 Manual.Count131072.C030709.packed 128 cuts30709 = true := by
 decide +kernel
def pointBounds30709 : List (Nat × Nat × Nat) := [(4029058048,105525194852558,105525578340934)]
theorem point_links_checked30709 : (cuts30709.take 1).map (fun c => (4029022209-1+2*2^9*c.k,105525082445369+c.lower,105525465933680+c.upper)) = pointBounds30709 := by
 decide +kernel
def cuts30710 : List PrefixCut := [⟨30,95777094,95777152⟩,
⟨128,416146633,416146869⟩]
theorem checked30710 : checkPrefixCuts (2^48) 4029153281 9 Manual.Count131072.C030710.packed 128 cuts30710 = true := by
 decide +kernel
def pointBounds30710 : List (Nat × Nat × Nat) := [(4029184000,105525593823771,105525977312378)]
theorem point_links_checked30710 : (cuts30710.take 1).map (fun c => (4029153281-1+2*2^9*c.k,105525498046677+c.lower,105525881535226+c.upper)) = pointBounds30710 := by
 decide +kernel
def cuts30711 : List PrefixCut := [⟨25,78659065,78659112⟩,
⟨128,410824033,410824265⟩]
theorem checked30711 : checkPrefixCuts (2^48) 4029284353 9 Manual.Count131072.C030711.packed 128 cuts30711 = true := by
 decide +kernel
def pointBounds30711 : List (Nat × Nat × Nat) := [(4029309952,105525992852375,105526376341207)]
theorem point_links_checked30711 : (cuts30711.take 1).map (fun c => (4029284353-1+2*2^9*c.k,105525914193310+c.lower,105526297682095+c.upper)) = pointBounds30711 := by
 decide +kernel
def cuts30712 : List PrefixCut := [⟨20,65873115,65873150⟩,
⟨128,418285038,418285279⟩]
theorem checked30712 : checkPrefixCuts (2^48) 4029415425 9 Manual.Count131072.C030712.packed 128 cuts30712 = true := by
 decide +kernel
def pointBounds30712 : List (Nat × Nat × Nat) := [(4029435904,105526390890458,105526774379510)]
theorem point_links_checked30712 : (cuts30712.take 1).map (fun c => (4029415425-1+2*2^9*c.k,105526325017343+c.lower,105526708506360+c.upper)) = pointBounds30712 := by
 decide +kernel
def cuts30713 : List PrefixCut := [⟨15,49176244,49176268⟩,
⟨128,407793750,407793970⟩]
theorem checked30713 : checkPrefixCuts (2^48) 4029546497 9 Manual.Count131072.C030713.packed 128 cuts30713 = true := by
 decide +kernel
def pointBounds30713 : List (Nat × Nat × Nat) := [(4029561856,105526792478625,105527175967907)]
theorem point_links_checked30713 : (cuts30713.take 1).map (fun c => (4029546497-1+2*2^9*c.k,105526743302381+c.lower,105527126791639+c.upper)) = pointBounds30713 := by
 decide +kernel
def cuts30714 : List PrefixCut := [⟨10,31921627,31921645⟩,
⟨128,411552311,411552543⟩]
theorem checked30714 : checkPrefixCuts (2^48) 4029677569 9 Manual.Count131072.C030714.packed 128 cuts30714 = true := by
 decide +kernel
def pointBounds30714 : List (Nat × Nat × Nat) := [(4029687808,105527183017758,105527566507254)]
theorem point_links_checked30714 : (cuts30714.take 1).map (fun c => (4029677569-1+2*2^9*c.k,105527151096131+c.lower,105527534585609+c.upper)) = pointBounds30714 := by
 decide +kernel
def cuts30715 : List PrefixCut := [⟨5,16833407,16833417⟩,
⟨128,412726335,412726566⟩]
theorem checked30715 : checkPrefixCuts (2^48) 4029808641 9 Manual.Count131072.C030715.packed 128 cuts30715 = true := by
 decide +kernel
def pointBounds30715 : List (Nat × Nat × Nat) := [(4029813760,105527579481849,105527962971569),(4029939712,105527975374777,105528358864718)]
theorem point_links_checked30715 : (cuts30715.take 2).map (fun c => (4029808641-1+2*2^9*c.k,105527562648442+c.lower,105527946138152+c.upper)) = pointBounds30715 := by
 decide +kernel
def cuts30716 : List PrefixCut := [⟨123,401677688,401677915⟩,
⟨128,417182991,417183227⟩]
theorem checked30716 : checkPrefixCuts (2^48) 4029939713 9 Manual.Count131072.C030716.packed 128 cuts30716 = true := by
 decide +kernel
def pointBounds30716 : List (Nat × Nat × Nat) := [(4030065664,105528377052465,105528760542633)]
theorem point_links_checked30716 : (cuts30716.take 1).map (fun c => (4029939713-1+2*2^9*c.k,105527975374777+c.lower,105528358864718+c.upper)) = pointBounds30716 := by
 decide +kernel
def cuts30717 : List PrefixCut := [⟨118,379873988,379874200⟩,
⟨128,413677263,413677494⟩]
theorem checked30717 : checkPrefixCuts (2^48) 4030070785 9 Manual.Count131072.C030717.packed 128 cuts30717 = true := by
 decide +kernel
def pointBounds30717 : List (Nat × Nat × Nat) := [(4030191616,105528772431756,105529155922145)]
theorem point_links_checked30717 : (cuts30717.take 1).map (fun c => (4030070785-1+2*2^9*c.k,105528392557768+c.lower,105528776047945+c.upper)) = pointBounds30717 := by
 decide +kernel
def cuts30718 : List PrefixCut := [⟨113,367011235,367011436⟩,
⟨128,417365332,417365561⟩]
theorem checked30718 : checkPrefixCuts (2^48) 4030201857 9 Manual.Count131072.C030718.packed 128 cuts30718 = true := by
 decide +kernel
def pointBounds30718 : List (Nat × Nat × Nat) := [(4030317568,105529173246266,105529556736875)]
theorem point_links_checked30718 : (cuts30718.take 1).map (fun c => (4030201857-1+2*2^9*c.k,105528806235031+c.lower,105529189725439+c.upper)) = pointBounds30718 := by
 decide +kernel
def cuts30719 : List PrefixCut := [⟨108,348073423,348073620⟩,
⟨128,411974302,411974537⟩]
theorem checked30719 : checkPrefixCuts (2^48) 4030332929 9 Manual.Count131072.C030719.packed 128 cuts30719 = true := by
 decide +kernel
def pointBounds30719 : List (Nat × Nat × Nat) := [(4030443520,105529571673786,105529955164620)]
theorem point_links_checked30719 : (cuts30719.take 1).map (fun c => (4030332929-1+2*2^9*c.k,105529223600363+c.lower,105529607091000+c.upper)) = pointBounds30719 := by
 decide +kernel
def cuts30720 : List PrefixCut := [⟨103,328438425,328438611⟩,
⟨128,407631083,407631310⟩]
theorem checked30720 : checkPrefixCuts (2^48) 4030464001 9 Manual.Count131072.C030720.packed 128 cuts30720 = true := by
 decide +kernel
def pointBounds30720 : List (Nat × Nat × Nat) := [(4030569472,105529964013090,105530347504148)]
theorem point_links_checked30720 : (cuts30720.take 1).map (fun c => (4030464001-1+2*2^9*c.k,105529635574665+c.lower,105530019065537+c.upper)) = pointBounds30720 := by
 decide +kernel
def cuts30721 : List PrefixCut := [⟨99,325215511,325215694⟩,
⟨128,417394493,417394728⟩]
theorem checked30721 : checkPrefixCuts (2^48) 4030595073 9 Manual.Count131072.C030721.packed 128 cuts30721 = true := by
 decide +kernel
def pointBounds30721 : List (Nat × Nat × Nat) := [(4030696448,105530368421259,105530751912541)]
theorem point_links_checked30721 : (cuts30721.take 1).map (fun c => (4030595073-1+2*2^9*c.k,105530043205748+c.lower,105530426696847+c.upper)) = pointBounds30721 := by
 decide +kernel
def cuts30722 : List PrefixCut := [⟨95,308096392,308096565⟩,
⟨128,415216112,415216348⟩]
theorem checked30722 : checkPrefixCuts (2^48) 4030726145 9 Manual.Count131072.C030722.packed 128 cuts30722 = true := by
 decide +kernel
def pointBounds30722 : List (Nat × Nat × Nat) := [(4030823424,105530768696633,105531152188140)]
theorem point_links_checked30722 : (cuts30722.take 1).map (fun c => (4030726145-1+2*2^9*c.k,105530460600241+c.lower,105530844091575+c.upper)) = pointBounds30722 := by
 decide +kernel
def cuts30723 : List PrefixCut := [⟨91,293911189,293911356⟩,
⟨128,409267204,409267439⟩]
theorem checked30723 : checkPrefixCuts (2^48) 4030857217 9 Manual.Count131072.C030723.packed 128 cuts30723 = true := by
 decide +kernel
def pointBounds30723 : List (Nat × Nat × Nat) := [(4030950400,105531169727542,105531553219279)]
theorem point_links_checked30723 : (cuts30723.take 1).map (fun c => (4030857217-1+2*2^9*c.k,105530875816353+c.lower,105531259307923+c.upper)) = pointBounds30723 := by
 decide +kernel
def cuts30724 : List PrefixCut := [⟨87,282170864,282171024⟩,
⟨128,414002077,414002309⟩]
theorem checked30724 : checkPrefixCuts (2^48) 4030988289 9 Manual.Count131072.C030724.packed 128 cuts30724 = true := by
 decide +kernel
def pointBounds30724 : List (Nat × Nat × Nat) := [(4031077376,105531567254421,105531950746386)]
theorem point_links_checked30724 : (cuts30724.take 1).map (fun c => (4030988289-1+2*2^9*c.k,105531285083557+c.lower,105531668575362+c.upper)) = pointBounds30724 := by
 decide +kernel
def cuts30725 : List PrefixCut := [⟨83,271199371,271199526⟩,
⟨128,420202963,420203197⟩]
theorem checked30725 : checkPrefixCuts (2^48) 4031119361 9 Manual.Count131072.C030725.packed 128 cuts30725 = true := by
 decide +kernel
def pointBounds30725 : List (Nat × Nat × Nat) := [(4031204352,105531970285005,105532353777197)]
theorem point_links_checked30725 : (cuts30725.take 1).map (fun c => (4031119361-1+2*2^9*c.k,105531699085634+c.lower,105532082577671+c.upper)) = pointBounds30725 := by
 decide +kernel
def cuts30726 : List PrefixCut := [⟨79,256737387,256737528⟩,
⟨128,411461579,411461804⟩]
theorem checked30726 : checkPrefixCuts (2^48) 4031250433 9 Manual.Count131072.C030726.packed 128 cuts30726 = true := by
 decide +kernel
def pointBounds30726 : List (Nat × Nat × Nat) := [(4031331328,105532376025984,105532759518396)]
theorem point_links_checked30726 : (cuts30726.take 1).map (fun c => (4031250433-1+2*2^9*c.k,105532119288597+c.lower,105532502780868+c.upper)) = pointBounds30726 := by
 decide +kernel
def cuts30727 : List PrefixCut := [⟨75,238645731,238645869⟩,
⟨128,409144083,409144314⟩]
theorem checked30727 : checkPrefixCuts (2^48) 4031381505 9 Manual.Count131072.C030727.packed 128 cuts30727 = true := by
 decide +kernel
def pointBounds30727 : List (Nat × Nat × Nat) := [(4031458304,105532769395907,105533152888541)]
theorem point_links_checked30727 : (cuts30727.take 1).map (fun c => (4031381505-1+2*2^9*c.k,105532530750176+c.lower,105532914242672+c.upper)) = pointBounds30727 := by
 decide +kernel
def cuts30728 : List PrefixCut := [⟨71,233750853,233750988⟩,
⟨128,419463849,419464088⟩]
theorem checked30728 : checkPrefixCuts (2^48) 4031512577 9 Manual.Count131072.C030728.packed 128 cuts30728 = true := by
 decide +kernel
def pointBounds30728 : List (Nat × Nat × Nat) := [(4031585280,105533173645112,105533557137974)]
theorem point_links_checked30728 : (cuts30728.take 1).map (fun c => (4031512577-1+2*2^9*c.k,105532939894259+c.lower,105533323386986+c.upper)) = pointBounds30728 := by
 decide +kernel
def cuts30729 : List PrefixCut := [⟨67,215940349,215940468⟩,
⟨128,414004591,414004824⟩]
theorem checked30729 : checkPrefixCuts (2^48) 4031643649 9 Manual.Count131072.C030729.packed 128 cuts30729 = true := by
 decide +kernel
def pointBounds30729 : List (Nat × Nat × Nat) := [(4031712256,105533575298457,105533958791542)]
theorem point_links_checked30729 : (cuts30729.take 1).map (fun c => (4031643649-1+2*2^9*c.k,105533359358108+c.lower,105533742851074+c.upper)) = pointBounds30729 := by
 decide +kernel
def cuts30730 : List PrefixCut := [⟨63,201202749,201202861⟩,
⟨128,409592904,409593135⟩]
theorem checked30730 : checkPrefixCuts (2^48) 4031774721 9 Manual.Count131072.C030730.packed 128 cuts30730 = true := by
 decide +kernel
def pointBounds30730 : List (Nat × Nat × Nat) := [(4031839232,105533974565448,105534358058759)]
theorem point_links_checked30730 : (cuts30730.take 1).map (fun c => (4031774721-1+2*2^9*c.k,105533773362699+c.lower,105534156855898+c.upper)) = pointBounds30730 := by
 decide +kernel
def cuts30731 : List PrefixCut := [⟨59,189188738,189188844⟩,
⟨128,406228706,406228938⟩]
theorem checked30731 : checkPrefixCuts (2^48) 4031905793 9 Manual.Count131072.C030731.packed 128 cuts30731 = true := by
 decide +kernel
def pointBounds30731 : List (Nat × Nat × Nat) := [(4031966208,105534372144341,105534755637877)]
theorem point_links_checked30731 : (cuts30731.take 1).map (fun c => (4031905793-1+2*2^9*c.k,105534182955603+c.lower,105534566449033+c.upper)) = pointBounds30731 := by
 decide +kernel
def cuts30732 : List PrefixCut := [⟨55,176267998,176268100⟩,
⟨128,411311474,411311704⟩]
theorem checked30732 : checkPrefixCuts (2^48) 4032036865 9 Manual.Count131072.C030732.packed 128 cuts30732 = true := by
 decide +kernel
def pointBounds30732 : List (Nat × Nat × Nat) := [(4032093184,105534765452307,105535148946071)]
theorem point_links_checked30732 : (cuts30732.take 1).map (fun c => (4032036865-1+2*2^9*c.k,105534589184309+c.lower,105534972677971+c.upper)) = pointBounds30732 := by
 decide +kernel
def cuts30733 : List PrefixCut := [⟨51,173190880,173190971⟩,
⟨128,425119812,425120047⟩]
theorem checked30733 : checkPrefixCuts (2^48) 4032167937 9 Manual.Count131072.C030733.packed 128 cuts30733 = true := by
 decide +kernel
def pointBounds30733 : List (Nat × Nat × Nat) := [(4032220160,105535173686663,105535557180646)]
theorem point_links_checked30733 : (cuts30733.take 1).map (fun c => (4032167937-1+2*2^9*c.k,105535000495783+c.lower,105535383989675+c.upper)) = pointBounds30733 := by
 decide +kernel
def cuts30734 : List PrefixCut := [⟨47,151336492,151336577⟩,
⟨128,409120917,409121145⟩]
theorem checked30734 : checkPrefixCuts (2^48) 4032299009 9 Manual.Count131072.C030734.packed 128 cuts30734 = true := by
 decide +kernel
def pointBounds30734 : List (Nat × Nat × Nat) := [(4032347136,105535576952087,105535960446299)]
theorem point_links_checked30734 : (cuts30734.take 1).map (fun c => (4032299009-1+2*2^9*c.k,105535425615595+c.lower,105535809109722+c.upper)) = pointBounds30734 := by
 decide +kernel
def cuts30735 : List PrefixCut := [⟨43,138697394,138697476⟩,
⟨128,411760006,411760246⟩]
theorem checked30735 : checkPrefixCuts (2^48) 4032430081 9 Manual.Count131072.C030735.packed 128 cuts30735 = true := by
 decide +kernel
def pointBounds30735 : List (Nat × Nat × Nat) := [(4032474112,105535973433906,105536356928343)]
theorem point_links_checked30735 : (cuts30735.take 1).map (fun c => (4032430081-1+2*2^9*c.k,105535834736512+c.lower,105536218230867+c.upper)) = pointBounds30735 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S4.B000022
