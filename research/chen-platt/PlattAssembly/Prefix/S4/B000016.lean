import PlattAssemblyKernel
import PlattCertificates.Count131072.C030512
import PlattCertificates.Count131072.C030513
import PlattCertificates.Count131072.C030514
import PlattCertificates.Count131072.C030515
import PlattCertificates.Count131072.C030516
import PlattCertificates.Count131072.C030517
import PlattCertificates.Count131072.C030518
import PlattCertificates.Count131072.C030519
import PlattCertificates.Count131072.C030520
import PlattCertificates.Count131072.C030521
import PlattCertificates.Count131072.C030522
import PlattCertificates.Count131072.C030523
import PlattCertificates.Count131072.C030524
import PlattCertificates.Count131072.C030525
import PlattCertificates.Count131072.C030526
import PlattCertificates.Count131072.C030527
import PlattCertificates.Count131072.C030528
import PlattCertificates.Count131072.C030529
import PlattCertificates.Count131072.C030530
import PlattCertificates.Count131072.C030531
import PlattCertificates.Count131072.C030532
import PlattCertificates.Count131072.C030533
import PlattCertificates.Count131072.C030534
import PlattCertificates.Count131072.C030535
import PlattCertificates.Count131072.C030536
import PlattCertificates.Count131072.C030537
import PlattCertificates.Count131072.C030538
import PlattCertificates.Count131072.C030539
import PlattCertificates.Count131072.C030540
import PlattCertificates.Count131072.C030541
import PlattCertificates.Count131072.C030542
import PlattCertificates.Count131072.C030543
namespace ChenEffective.PlattWindow.Assembly.Prefix.S4.B000016
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts30512 : List PrefixCut := [⟨36,115593146,115593215⟩,
⟨128,413078932,413079171⟩]
theorem checked30512 : checkPrefixCuts (2^48) 4003201025 9 Manual.Count131072.C030512.packed 128 cuts30512 = true := by
 decide +kernel
def pointBounds30512 : List (Nat × Nat × Nat) := [(4003237888,105443410251319,105443793693751)]
theorem point_links_checked30512 : (cuts30512.take 1).map (fun c => (4003201025-1+2*2^9*c.k,105443294658173+c.lower,105443678100536+c.upper)) = pointBounds30512 := by
 decide +kernel
def cuts30513 : List PrefixCut := [⟨31,102722728,102722785⟩,
⟨128,415596556,415596784⟩]
theorem checked30513 : checkPrefixCuts (2^48) 4003332097 9 Manual.Count131072.C030513.packed 128 cuts30513 = true := by
 decide +kernel
def pointBounds30513 : List (Nat × Nat × Nat) := [(4003363840,105443810459833,105444193902492)]
theorem point_links_checked30513 : (cuts30513.take 1).map (fun c => (4003332097-1+2*2^9*c.k,105443707737105+c.lower,105444091179707+c.upper)) = pointBounds30513 := by
 decide +kernel
def cuts30514 : List PrefixCut := [⟨26,86267446,86267493⟩,
⟨128,415582941,415583169⟩]
theorem checked30514 : checkPrefixCuts (2^48) 4003463169 9 Manual.Count131072.C030514.packed 128 cuts30514 = true := by
 decide +kernel
def pointBounds30514 : List (Nat × Nat × Nat) := [(4003489792,105444209601107,105444593043984)]
theorem point_links_checked30514 : (cuts30514.take 1).map (fun c => (4003463169-1+2*2^9*c.k,105444123333661+c.lower,105444506776491+c.upper)) = pointBounds30514 := by
 decide +kernel
def cuts30515 : List PrefixCut := [⟨21,69953837,69953872⟩,
⟨128,416272384,416272608⟩]
theorem checked30515 : checkPrefixCuts (2^48) 4003594241 9 Manual.Count131072.C030515.packed 128 cuts30515 = true := by
 decide +kernel
def pointBounds30515 : List (Nat × Nat × Nat) := [(4003615744,105444608870439,105444992313532)]
theorem point_links_checked30515 : (cuts30515.take 1).map (fun c => (4003594241-1+2*2^9*c.k,105444538916602+c.lower,105444922359660+c.upper)) = pointBounds30515 := by
 decide +kernel
def cuts30516 : List PrefixCut := [⟨16,54063086,54063113⟩,
⟨128,416047863,416048093⟩]
theorem checked30516 : checkPrefixCuts (2^48) 4003725313 9 Manual.Count131072.C030516.packed 128 cuts30516 = true := by
 decide +kernel
def pointBounds30516 : List (Nat × Nat × Nat) := [(4003741696,105445009252072,105445392695381)]
theorem point_links_checked30516 : (cuts30516.take 1).map (fun c => (4003725313-1+2*2^9*c.k,105444955188986+c.lower,105445338632268+c.upper)) = pointBounds30516 := by
 decide +kernel
def cuts30517 : List PrefixCut := [⟨11,36837644,36837665⟩,
⟨128,415682696,415682931⟩]
theorem checked30517 : checkPrefixCuts (2^48) 4003856385 9 Manual.Count131072.C030517.packed 128 cuts30517 = true := by
 decide +kernel
def pointBounds30517 : List (Nat × Nat × Nat) := [(4003867648,105445408074493,105445791518026)]
theorem point_links_checked30517 : (cuts30517.take 1).map (fun c => (4003856385-1+2*2^9*c.k,105445371236849+c.lower,105445754680361+c.upper)) = pointBounds30517 := by
 decide +kernel
def cuts30518 : List PrefixCut := [⟨6,20527190,20527201⟩,
⟨128,416512644,416512882⟩]
theorem checked30518 : checkPrefixCuts (2^48) 4003987457 9 Manual.Count131072.C030518.packed 128 cuts30518 = true := by
 decide +kernel
def pointBounds30518 : List (Nat × Nat × Nat) := [(4003993600,105445807446735,105446190890493)]
theorem point_links_checked30518 : (cuts30518.take 1).map (fun c => (4003987457-1+2*2^9*c.k,105445786919545+c.lower,105446170363292+c.upper)) = pointBounds30518 := by
 decide +kernel
def cuts30519 : List PrefixCut := [⟨1,2882150,2882151⟩,
⟨124,397167984,397168207⟩,
⟨128,409258566,409258796⟩]
theorem checked30519 : checkPrefixCuts (2^48) 4004118529 9 Manual.Count131072.C030519.packed 128 cuts30519 = true := by
 decide +kernel
def pointBounds30519 : List (Nat × Nat × Nat) := [(4004119552,105446206314339,105446589758325),(4004245504,105446600600173,105446984044381)]
theorem point_links_checked30519 : (cuts30519.take 2).map (fun c => (4004118529-1+2*2^9*c.k,105446203432189+c.lower,105446586876174+c.upper)) = pointBounds30519 := by
 decide +kernel
def cuts30520 : List PrefixCut := [⟨119,388157840,388158061⟩,
⟨128,417539820,417540058⟩]
theorem checked30520 : checkPrefixCuts (2^48) 4004249601 9 Manual.Count131072.C030520.packed 128 cuts30520 = true := by
 decide +kernel
def pointBounds30520 : List (Nat × Nat × Nat) := [(4004371456,105447000848595,105447384293031)]
theorem point_links_checked30520 : (cuts30520.take 1).map (fun c => (4004249601-1+2*2^9*c.k,105446612690755+c.lower,105446996134970+c.upper)) = pointBounds30520 := by
 decide +kernel
def cuts30521 : List PrefixCut := [⟨114,371416136,371416340⟩,
⟨128,416963774,416964004⟩]
theorem checked30521 : checkPrefixCuts (2^48) 4004380673 9 Manual.Count131072.C030521.packed 128 cuts30521 = true := by
 decide +kernel
def pointBounds30521 : List (Nat × Nat × Nat) := [(4004497408,105447401646711,105447785091368)]
theorem point_links_checked30521 : (cuts30521.take 1).map (fun c => (4004380673-1+2*2^9*c.k,105447030230575+c.lower,105447413675028+c.upper)) = pointBounds30521 := by
 decide +kernel
def cuts30522 : List PrefixCut := [⟨109,351512644,351512836⟩,
⟨128,416387836,416388064⟩]
theorem checked30522 : checkPrefixCuts (2^48) 4004511745 9 Manual.Count131072.C030522.packed 128 cuts30522 = true := by
 decide +kernel
def pointBounds30522 : List (Nat × Nat × Nat) := [(4004623360,105447798706993,105448182151868)]
theorem point_links_checked30522 : (cuts30522.take 1).map (fun c => (4004511745-1+2*2^9*c.k,105447447194349+c.lower,105447830639032+c.upper)) = pointBounds30522 := by
 decide +kernel
def cuts30523 : List PrefixCut := [⟨104,342223547,342223736⟩,
⟨128,422629658,422629891⟩]
theorem checked30523 : checkPrefixCuts (2^48) 4004642817 9 Manual.Count131072.C030523.packed 128 cuts30523 = true := by
 decide +kernel
def pointBounds30523 : List (Nat × Nat × Nat) := [(4004749312,105448205805732,105448589250832)]
theorem point_links_checked30523 : (cuts30523.take 1).map (fun c => (4004642817-1+2*2^9*c.k,105447863582185+c.lower,105448247027096+c.upper)) = pointBounds30523 := by
 decide +kernel
def cuts30524 : List PrefixCut := [⟨99,321478785,321478968⟩,
⟨128,416711982,416712218⟩]
theorem checked30524 : checkPrefixCuts (2^48) 4004773889 9 Manual.Count131072.C030524.packed 128 cuts30524 = true := by
 decide +kernel
def pointBounds30524 : List (Nat × Nat × Nat) := [(4004875264,105448607690628,105448991135955)]
theorem point_links_checked30524 : (cuts30524.take 1).map (fun c => (4004773889-1+2*2^9*c.k,105448286211843+c.lower,105448669656987+c.upper)) = pointBounds30524 := by
 decide +kernel
def cuts30525 : List PrefixCut := [⟨94,302422152,302422325⟩,
⟨128,415854954,415855191⟩]
theorem checked30525 : checkPrefixCuts (2^48) 4004904961 9 Manual.Count131072.C030525.packed 128 cuts30525 = true := by
 decide +kernel
def pointBounds30525 : List (Nat × Nat × Nat) := [(4005001216,105449005345977,105449388791530)]
theorem point_links_checked30525 : (cuts30525.take 1).map (fun c => (4004904961-1+2*2^9*c.k,105448702923825+c.lower,105449086369205+c.upper)) = pointBounds30525 := by
 decide +kernel
def cuts30526 : List PrefixCut := [⟨89,294681683,294681842⟩,
⟨128,418441756,418441987⟩]
theorem checked30526 : checkPrefixCuts (2^48) 4005036033 9 Manual.Count131072.C030526.packed 128 cuts30526 = true := by
 decide +kernel
def pointBounds30526 : List (Nat × Nat × Nat) := [(4005127168,105449413460462,105449796906238)]
theorem point_links_checked30526 : (cuts30526.take 1).map (fun c => (4005036033-1+2*2^9*c.k,105449118778779+c.lower,105449502224396+c.upper)) = pointBounds30526 := by
 decide +kernel
def cuts30527 : List PrefixCut := [⟨84,271691636,271691785⟩,
⟨128,418076625,418076855⟩]
theorem checked30527 : checkPrefixCuts (2^48) 4005167105 9 Manual.Count131072.C030527.packed 128 cuts30527 = true := by
 decide +kernel
def pointBounds30527 : List (Nat × Nat × Nat) := [(4005253120,105449808912171,105450192358168)]
theorem point_links_checked30527 : (cuts30527.take 1).map (fun c => (4005167105-1+2*2^9*c.k,105449537220535+c.lower,105449920666383+c.upper)) = pointBounds30527 := by
 decide +kernel
def cuts30528 : List PrefixCut := [⟨79,260368611,260368757⟩,
⟨128,417149422,417149653⟩]
theorem checked30528 : checkPrefixCuts (2^48) 4005298177 9 Manual.Count131072.C030528.packed 128 cuts30528 = true := by
 decide +kernel
def pointBounds30528 : List (Nat × Nat × Nat) := [(4005379072,105450215665771,105450599111995)]
theorem point_links_checked30528 : (cuts30528.take 1).map (fun c => (4005298177-1+2*2^9*c.k,105449955297160+c.lower,105450338743238+c.upper)) = pointBounds30528 := by
 decide +kernel
def cuts30529 : List PrefixCut := [⟨74,240402806,240402939⟩,
⟨128,415378883,415379113⟩]
theorem checked30529 : checkPrefixCuts (2^48) 4005429249 9 Manual.Count131072.C030529.packed 128 cuts30529 = true := by
 decide +kernel
def pointBounds30529 : List (Nat × Nat × Nat) := [(4005505024,105450612849388,105450996295830)]
theorem point_links_checked30529 : (cuts30529.take 1).map (fun c => (4005429249-1+2*2^9*c.k,105450372446582+c.lower,105450755892891+c.upper)) = pointBounds30529 := by
 decide +kernel
def cuts30530 : List PrefixCut := [⟨69,224303194,224303320⟩,
⟨128,421478792,421479030⟩]
theorem checked30530 : checkPrefixCuts (2^48) 4005560321 9 Manual.Count131072.C030530.packed 128 cuts30530 = true := by
 decide +kernel
def pointBounds30530 : List (Nat × Nat × Nat) := [(4005630976,105451012128659,105451395575324)]
theorem point_links_checked30530 : (cuts30530.take 1).map (fun c => (4005560321-1+2*2^9*c.k,105450787825465+c.lower,105451171272004+c.upper)) = pointBounds30530 := by
 decide +kernel
def cuts30531 : List PrefixCut := [⟨64,207291091,207291205⟩,
⟨128,415140931,415141158⟩]
theorem checked30531 : checkPrefixCuts (2^48) 4005691393 9 Manual.Count131072.C030531.packed 128 cuts30531 = true := by
 decide +kernel
def pointBounds30531 : List (Nat × Nat × Nat) := [(4005756928,105451416595348,105451800042239)]
theorem point_links_checked30531 : (cuts30531.take 1).map (fun c => (4005691393-1+2*2^9*c.k,105451209304257+c.lower,105451592751034+c.upper)) = pointBounds30531 := by
 decide +kernel
def cuts30532 : List PrefixCut := [⟨59,190701714,190701823⟩,
⟨128,416954277,416954515⟩]
theorem checked30532 : checkPrefixCuts (2^48) 4005822465 9 Manual.Count131072.C030532.packed 128 cuts30532 = true := by
 decide +kernel
def pointBounds30532 : List (Nat × Nat × Nat) := [(4005882880,105451815146902,105452198594015)]
theorem point_links_checked30532 : (cuts30532.take 1).map (fun c => (4005822465-1+2*2^9*c.k,105451624445188+c.lower,105452007892192+c.upper)) = pointBounds30532 := by
 decide +kernel
def cuts30533 : List PrefixCut := [⟨54,177977850,177977947⟩,
⟨128,418486456,418486691⟩]
theorem checked30533 : checkPrefixCuts (2^48) 4005953537 9 Manual.Count131072.C030533.packed 128 cuts30533 = true := by
 decide +kernel
def pointBounds30533 : List (Nat × Nat × Nat) := [(4006008832,105452219377315,105452602824654)]
theorem point_links_checked30533 : (cuts30533.take 1).map (fun c => (4005953537-1+2*2^9*c.k,105452041399465+c.lower,105452424846707+c.upper)) = pointBounds30533 := by
 decide +kernel
def cuts30534 : List PrefixCut := [⟨49,156612664,156612752⟩,
⟨128,413484158,413484389⟩]
theorem checked30534 : checkPrefixCuts (2^48) 4006084609 9 Manual.Count131072.C030534.packed 128 cuts30534 = true := by
 decide +kernel
def pointBounds30534 : List (Nat × Nat × Nat) := [(4006134784,105452616498585,105452999946150)]
theorem point_links_checked30534 : (cuts30534.take 1).map (fun c => (4006084609-1+2*2^9*c.k,105452459885921+c.lower,105452843333398+c.upper)) = pointBounds30534 := by
 decide +kernel
def cuts30535 : List PrefixCut := [⟨44,143047628,143047705⟩,
⟨128,416913287,416913518⟩]
theorem checked30535 : checkPrefixCuts (2^48) 4006215681 9 Manual.Count131072.C030535.packed 128 cuts30535 = true := by
 decide +kernel
def pointBounds30535 : List (Nat × Nat × Nat) := [(4006260736,105453016417707,105453399865492)]
theorem point_links_checked30535 : (cuts30535.take 1).map (fun c => (4006215681-1+2*2^9*c.k,105452873370079+c.lower,105453256817787+c.upper)) = pointBounds30535 := by
 decide +kernel
def cuts30536 : List PrefixCut := [⟨39,125408562,125408634⟩,
⟨128,413176119,413176349⟩]
theorem checked30536 : checkPrefixCuts (2^48) 4006346753 9 Manual.Count131072.C030536.packed 128 cuts30536 = true := by
 decide +kernel
def pointBounds30536 : List (Nat × Nat × Nat) := [(4006386688,105453415691928,105453799139939)]
theorem point_links_checked30536 : (cuts30536.take 1).map (fun c => (4006346753-1+2*2^9*c.k,105453290283366+c.lower,105453673731305+c.upper)) = pointBounds30536 := by
 decide +kernel
def cuts30537 : List PrefixCut := [⟨34,109667502,109667561⟩,
⟨128,406558770,406558999⟩]
theorem checked30537 : checkPrefixCuts (2^48) 4006477825 9 Manual.Count131072.C030537.packed 128 cuts30537 = true := by
 decide +kernel
def pointBounds30537 : List (Nat × Nat × Nat) := [(4006512640,105453813126987,105454196575215)]
theorem point_links_checked30537 : (cuts30537.take 1).map (fun c => (4006477825-1+2*2^9*c.k,105453703459485+c.lower,105454086907654+c.upper)) = pointBounds30537 := by
 decide +kernel
def cuts30538 : List PrefixCut := [⟨29,91468614,91468662⟩,
⟨128,408933967,408934195⟩]
theorem checked30538 : checkPrefixCuts (2^48) 4006608897 9 Manual.Count131072.C030538.packed 128 cuts30538 = true := by
 decide +kernel
def pointBounds30538 : List (Nat × Nat × Nat) := [(4006638592,105454201486869,105454584935315)]
theorem point_links_checked30538 : (cuts30538.take 1).map (fun c => (4006608897-1+2*2^9*c.k,105454110018255+c.lower,105454493466653+c.upper)) = pointBounds30538 := by
 decide +kernel
def cuts30539 : List PrefixCut := [⟨24,76853648,76853688⟩,
⟨128,416156268,416156495⟩]
theorem checked30539 : checkPrefixCuts (2^48) 4006739969 9 Manual.Count131072.C030539.packed 128 cuts30539 = true := by
 decide +kernel
def pointBounds30539 : List (Nat × Nat × Nat) := [(4006764544,105454595805870,105454979254536)]
theorem point_links_checked30539 : (cuts30539.take 1).map (fun c => (4006739969-1+2*2^9*c.k,105454518952222+c.lower,105454902400848+c.upper)) = pointBounds30539 := by
 decide +kernel
def cuts30540 : List PrefixCut := [⟨19,63574337,63574374⟩,
⟨128,417336898,417337137⟩]
theorem checked30540 : checkPrefixCuts (2^48) 4006871041 9 Manual.Count131072.C030540.packed 128 cuts30540 = true := by
 decide +kernel
def pointBounds30540 : List (Nat × Nat × Nat) := [(4006890496,105454998682827,105455382131717)]
theorem point_links_checked30540 : (cuts30540.take 1).map (fun c => (4006871041-1+2*2^9*c.k,105454935108490+c.lower,105455318557343+c.upper)) = pointBounds30540 := by
 decide +kernel
def cuts30541 : List PrefixCut := [⟨14,46151383,46151408⟩,
⟨128,415356410,415356637⟩]
theorem checked30541 : checkPrefixCuts (2^48) 4007002113 9 Manual.Count131072.C030541.packed 128 cuts30541 = true := by
 decide +kernel
def pointBounds30541 : List (Nat × Nat × Nat) := [(4007016448,105455398596771,105455782045888)]
theorem point_links_checked30541 : (cuts30541.take 1).map (fun c => (4007002113-1+2*2^9*c.k,105455352445388+c.lower,105455735894480+c.upper)) = pointBounds30541 := by
 decide +kernel
def cuts30542 : List PrefixCut := [⟨9,30345139,30345155⟩,
⟨128,415975026,415975255⟩]
theorem checked30542 : checkPrefixCuts (2^48) 4007133185 9 Manual.Count131072.C030542.packed 128 cuts30542 = true := by
 decide +kernel
def pointBounds30542 : List (Nat × Nat × Nat) := [(4007142400,105455798146937,105456181596272)]
theorem point_links_checked30542 : (cuts30542.take 1).map (fun c => (4007133185-1+2*2^9*c.k,105455767801798+c.lower,105456151251117+c.upper)) = pointBounds30542 := by
 decide +kernel
def cuts30543 : List PrefixCut := [⟨4,13416056,13416063⟩,
⟨127,414626850,414627084⟩,
⟨128,417857838,417858074⟩]
theorem checked30543 : checkPrefixCuts (2^48) 4007264257 9 Manual.Count131072.C030543.packed 128 cuts30543 = true := by
 decide +kernel
def pointBounds30543 : List (Nat × Nat × Nat) := [(4007268352,105456197192880,105456580642435),(4007394304,105456598403674,105456981853456)]
theorem point_links_checked30543 : (cuts30543.take 2).map (fun c => (4007264257-1+2*2^9*c.k,105456183776824+c.lower,105456567226372+c.upper)) = pointBounds30543 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S4.B000016
