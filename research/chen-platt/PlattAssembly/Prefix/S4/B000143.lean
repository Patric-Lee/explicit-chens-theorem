import PlattAssemblyKernel
import PlattCertificates.Count131072.C034576
import PlattCertificates.Count131072.C034577
import PlattCertificates.Count131072.C034578
import PlattCertificates.Count131072.C034579
import PlattCertificates.Count131072.C034580
import PlattCertificates.Count131072.C034581
import PlattCertificates.Count131072.C034582
import PlattCertificates.Count131072.C034583
import PlattCertificates.Count131072.C034584
import PlattCertificates.Count131072.C034585
import PlattCertificates.Count131072.C034586
import PlattCertificates.Count131072.C034587
import PlattCertificates.Count131072.C034588
import PlattCertificates.Count131072.C034589
import PlattCertificates.Count131072.C034590
import PlattCertificates.Count131072.C034591
import PlattCertificates.Count131072.C034592
import PlattCertificates.Count131072.C034593
import PlattCertificates.Count131072.C034594
import PlattCertificates.Count131072.C034595
import PlattCertificates.Count131072.C034596
import PlattCertificates.Count131072.C034597
import PlattCertificates.Count131072.C034598
import PlattCertificates.Count131072.C034599
import PlattCertificates.Count131072.C034600
import PlattCertificates.Count131072.C034601
import PlattCertificates.Count131072.C034602
import PlattCertificates.Count131072.C034603
import PlattCertificates.Count131072.C034604
import PlattCertificates.Count131072.C034605
import PlattCertificates.Count131072.C034606
import PlattCertificates.Count131072.C034607
namespace ChenEffective.PlattWindow.Assembly.Prefix.S4.B000143
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts34576 : List PrefixCut := [⟨64,365251757,365251986⟩]
theorem checked34576 : checkPrefixCuts (2^48) 4535877633 10 Manual.Count131072.C034576.packed 64 cuts34576 = true := by
 decide +kernel
def cuts34577 : List PrefixCut := [⟨3,16692360,16692372⟩,
⟨64,365551464,365551695⟩]
theorem checked34577 : checkPrefixCuts (2^48) 4536008705 10 Manual.Count131072.C034577.packed 64 cuts34577 = true := by
 decide +kernel
def pointBounds34577 : List (Nat × Nat × Nat) := [(4536014848,107029467982581,107029852369055)]
theorem point_links_checked34577 : (cuts34577.take 1).map (fun c => (4536008705-1+2*2^10*c.k,107029451290221+c.lower,107029835676683+c.upper)) = pointBounds34577 := by
 decide +kernel
def cuts34578 : List PrefixCut := [⟨9,53674553,53674587⟩,
⟨64,361073278,361073504⟩]
theorem checked34578 : checkPrefixCuts (2^48) 4536139777 10 Manual.Count131072.C034578.packed 64 cuts34578 = true := by
 decide +kernel
def pointBounds34578 : List (Nat × Nat × Nat) := [(4536158208,107029870516238,107030254902965)]
theorem point_links_checked34578 : (cuts34578.take 1).map (fun c => (4536139777-1+2*2^10*c.k,107029816841685+c.lower,107030201228378+c.upper)) = pointBounds34578 := by
 decide +kernel
def cuts34579 : List PrefixCut := [⟨15,86124888,86124943⟩,
⟨64,367081579,367081808⟩]
theorem checked34579 : checkPrefixCuts (2^48) 4536270849 10 Manual.Count131072.C034579.packed 64 cuts34579 = true := by
 decide +kernel
def pointBounds34579 : List (Nat × Nat × Nat) := [(4536301568,107030264039851,107030648426825)]
theorem point_links_checked34579 : (cuts34579.take 1).map (fun c => (4536270849-1+2*2^10*c.k,107030177914963+c.lower,107030562301882+c.upper)) = pointBounds34579 := by
 decide +kernel
def cuts34580 : List PrefixCut := [⟨21,119628076,119628150⟩,
⟨64,366264325,366264553⟩]
theorem checked34580 : checkPrefixCuts (2^48) 4536401921 10 Manual.Count131072.C034580.packed 64 cuts34580 = true := by
 decide +kernel
def pointBounds34580 : List (Nat × Nat × Nat) := [(4536444928,107030664624618,107031049011840)]
theorem point_links_checked34580 : (cuts34580.take 1).map (fun c => (4536401921-1+2*2^10*c.k,107030544996542+c.lower,107030929383690+c.upper)) = pointBounds34580 := by
 decide +kernel
def cuts34581 : List PrefixCut := [⟨27,152198543,152198639⟩,
⟨64,365571249,365571476⟩]
theorem checked34581 : checkPrefixCuts (2^48) 4536532993 10 Manual.Count131072.C034581.packed 64 cuts34581 = true := by
 decide +kernel
def pointBounds34581 : List (Nat × Nat × Nat) := [(4536588288,107031063459410,107031447846882)]
theorem point_links_checked34581 : (cuts34581.take 1).map (fun c => (4536532993-1+2*2^10*c.k,107030911260867+c.lower,107031295648243+c.upper)) = pointBounds34581 := by
 decide +kernel
def cuts34582 : List PrefixCut := [⟨33,193825448,193825569⟩,
⟨64,370027862,370028093⟩]
theorem checked34582 : checkPrefixCuts (2^48) 4536664065 10 Manual.Count131072.C034582.packed 64 cuts34582 = true := by
 decide +kernel
def pointBounds34582 : List (Nat × Nat × Nat) := [(4536731648,107031470657564,107031855045288)]
theorem point_links_checked34582 : (cuts34582.take 1).map (fun c => (4536664065-1+2*2^10*c.k,107031276832116+c.lower,107031661219719+c.upper)) = pointBounds34582 := by
 decide +kernel
def cuts34583 : List PrefixCut := [⟨39,222607136,222607277⟩,
⟨64,366915032,366915260⟩]
theorem checked34583 : checkPrefixCuts (2^48) 4536795137 10 Manual.Count131072.C034583.packed 64 cuts34583 = true := by
 decide +kernel
def pointBounds34583 : List (Nat × Nat × Nat) := [(4536875008,107031869467114,107032253855089)]
theorem point_links_checked34583 : (cuts34583.take 1).map (fun c => (4536795137-1+2*2^10*c.k,107031646859978+c.lower,107032031247812+c.upper)) = pointBounds34583 := by
 decide +kernel
def cuts34584 : List PrefixCut := [⟨45,261871885,261872048⟩,
⟨64,371619493,371619723⟩]
theorem checked34584 : checkPrefixCuts (2^48) 4536926209 10 Manual.Count131072.C034584.packed 64 cuts34584 = true := by
 decide +kernel
def pointBounds34584 : List (Nat × Nat × Nat) := [(4537018368,107032275646895,107032660035120)]
theorem point_links_checked34584 : (cuts34584.take 1).map (fun c => (4536926209-1+2*2^10*c.k,107032013775010+c.lower,107032398163072+c.upper)) = pointBounds34584 := by
 decide +kernel
def cuts34585 : List PrefixCut := [⟨51,289284920,289285099⟩,
⟨64,363357668,363357893⟩]
theorem checked34585 : checkPrefixCuts (2^48) 4537057281 10 Manual.Count131072.C034585.packed 64 cuts34585 = true := by
 decide +kernel
def pointBounds34585 : List (Nat × Nat × Nat) := [(4537161728,107032674679423,107033059067894)]
theorem point_links_checked34585 : (cuts34585.take 1).map (fun c => (4537057281-1+2*2^10*c.k,107032385394503+c.lower,107032769782795+c.upper)) = pointBounds34585 := by
 decide +kernel
def cuts34586 : List PrefixCut := [⟨57,327986964,327987171⟩,
⟨64,367875854,367876084⟩]
theorem checked34586 : checkPrefixCuts (2^48) 4537188353 10 Manual.Count131072.C034586.packed 64 cuts34586 = true := by
 decide +kernel
def pointBounds34586 : List (Nat × Nat × Nat) := [(4537305088,107033076739135,107033461127859)]
theorem point_links_checked34586 : (cuts34586.take 1).map (fun c => (4537188353-1+2*2^10*c.k,107032748752171+c.lower,107033133140688+c.upper)) = pointBounds34586 := by
 decide +kernel
def cuts34587 : List PrefixCut := [⟨63,360917414,360917640⟩,
⟨64,366562483,366562712⟩]
theorem checked34587 : checkPrefixCuts (2^48) 4537319425 10 Manual.Count131072.C034587.packed 64 cuts34587 = true := by
 decide +kernel
def pointBounds34587 : List (Nat × Nat × Nat) := [(4537448448,107033477545439,107033861934412)]
theorem point_links_checked34587 : (cuts34587.take 1).map (fun c => (4537319425-1+2*2^10*c.k,107033116628025+c.lower,107033501016772+c.upper)) = pointBounds34587 := by
 decide +kernel
def cuts34588 : List PrefixCut := [⟨64,362953984,362954209⟩]
theorem checked34588 : checkPrefixCuts (2^48) 4537450497 10 Manual.Count131072.C034588.packed 64 cuts34588 = true := by
 decide +kernel
def cuts34589 : List PrefixCut := [⟨5,29279033,29279050⟩,
⟨64,370573315,370573544⟩]
theorem checked34589 : checkPrefixCuts (2^48) 4537581569 10 Manual.Count131072.C034589.packed 64 cuts34589 = true := by
 decide +kernel
def pointBounds34589 : List (Nat × Nat × Nat) := [(4537591808,107033875423525,107034259812743)]
theorem point_links_checked34589 : (cuts34589.take 1).map (fun c => (4537581569-1+2*2^10*c.k,107033846144492+c.lower,107034230533693+c.upper)) = pointBounds34589 := by
 decide +kernel
def cuts34590 : List PrefixCut := [⟨11,63270571,63270611⟩,
⟨64,367585208,367585431⟩]
theorem checked34590 : checkPrefixCuts (2^48) 4537712641 10 Manual.Count131072.C034590.packed 64 cuts34590 = true := by
 decide +kernel
def pointBounds34590 : List (Nat × Nat × Nat) := [(4537735168,107034279988378,107034664377848)]
theorem point_links_checked34590 : (cuts34590.take 1).map (fun c => (4537712641-1+2*2^10*c.k,107034216717807+c.lower,107034601107237+c.upper)) = pointBounds34590 := by
 decide +kernel
def cuts34591 : List PrefixCut := [⟨17,97446133,97446196⟩,
⟨64,366458089,366458324⟩]
theorem checked34591 : checkPrefixCuts (2^48) 4537843713 10 Manual.Count131072.C034591.packed 64 cuts34591 = true := by
 decide +kernel
def pointBounds34591 : List (Nat × Nat × Nat) := [(4537878528,107034681749148,107035066138864)]
theorem point_links_checked34591 : (cuts34591.take 1).map (fun c => (4537843713-1+2*2^10*c.k,107034584303015+c.lower,107034968692668+c.upper)) = pointBounds34591 := by
 decide +kernel
def cuts34592 : List PrefixCut := [⟨23,132860156,132860242⟩,
⟨64,364276675,364276906⟩]
theorem checked34592 : checkPrefixCuts (2^48) 4537974785 10 Manual.Count131072.C034592.packed 64 cuts34592 = true := by
 decide +kernel
def pointBounds34592 : List (Nat × Nat × Nat) := [(4538021888,107035083621260,107035468011234)]
theorem point_links_checked34592 : (cuts34592.take 1).map (fun c => (4537974785-1+2*2^10*c.k,107034950761104+c.lower,107035335150992+c.upper)) = pointBounds34592 := by
 decide +kernel
def cuts34593 : List PrefixCut := [⟨29,166907507,166907611⟩,
⟨64,364638276,364638506⟩]
theorem checked34593 : checkPrefixCuts (2^48) 4538105857 10 Manual.Count131072.C034593.packed 64 cuts34593 = true := by
 decide +kernel
def pointBounds34593 : List (Nat × Nat × Nat) := [(4538165248,107035481945286,107035866335509)]
theorem point_links_checked34593 : (cuts34593.take 1).map (fun c => (4538105857-1+2*2^10*c.k,107035315037779+c.lower,107035699427898+c.upper)) = pointBounds34593 := by
 decide +kernel
def cuts34594 : List PrefixCut := [⟨35,199712346,199712472⟩,
⟨64,366240262,366240488⟩]
theorem checked34594 : checkPrefixCuts (2^48) 4538236929 10 Manual.Count131072.C034594.packed 64 cuts34594 = true := by
 decide +kernel
def pointBounds34594 : List (Nat × Nat × Nat) := [(4538308608,107035879388401,107036263778876)]
theorem point_links_checked34594 : (cuts34594.take 1).map (fun c => (4538236929-1+2*2^10*c.k,107035679676055+c.lower,107036064066404+c.upper)) = pointBounds34594 := by
 decide +kernel
def cuts34595 : List PrefixCut := [⟨41,231584912,231585062⟩,
⟨64,362446480,362446715⟩]
theorem checked34595 : checkPrefixCuts (2^48) 4538368001 10 Manual.Count131072.C034595.packed 64 cuts34595 = true := by
 decide +kernel
def pointBounds34595 : List (Nat × Nat × Nat) := [(4538451968,107036277501229,107036661891954)]
theorem point_links_checked34595 : (cuts34595.take 1).map (fun c => (4538368001-1+2*2^10*c.k,107036045916317+c.lower,107036430306892+c.upper)) = pointBounds34595 := by
 decide +kernel
def cuts34596 : List PrefixCut := [⟨47,267362677,267362843⟩,
⟨64,365412857,365413087⟩]
theorem checked34596 : checkPrefixCuts (2^48) 4538499073 10 Manual.Count131072.C034596.packed 64 cuts34596 = true := by
 decide +kernel
def pointBounds34596 : List (Nat × Nat × Nat) := [(4538595328,107036675725474,107037060116450)]
theorem point_links_checked34596 : (cuts34596.take 1).map (fun c => (4538499073-1+2*2^10*c.k,107036408362797+c.lower,107036792753607+c.upper)) = pointBounds34596 := by
 decide +kernel
def cuts34597 : List PrefixCut := [⟨53,302828257,302828451⟩,
⟨64,367324846,367325080⟩]
theorem checked34597 : checkPrefixCuts (2^48) 4538630145 10 Manual.Count131072.C034597.packed 64 cuts34597 = true := by
 decide +kernel
def pointBounds34597 : List (Nat × Nat × Nat) := [(4538738688,107037076603911,107037460995145)]
theorem point_links_checked34597 : (cuts34597.take 1).map (fun c => (4538630145-1+2*2^10*c.k,107036773775654+c.lower,107037158166694+c.upper)) = pointBounds34597 := by
 decide +kernel
def cuts34598 : List PrefixCut := [⟨59,340276179,340276393⟩,
⟨64,370539048,370539281⟩]
theorem checked34598 : checkPrefixCuts (2^48) 4538761217 10 Manual.Count131072.C034598.packed 64 cuts34598 = true := by
 decide +kernel
def pointBounds34598 : List (Nat × Nat × Nat) := [(4538882048,107037481376679,107037865768167)]
theorem point_links_checked34598 : (cuts34598.take 1).map (fun c => (4538761217-1+2*2^10*c.k,107037141100500+c.lower,107037525491774+c.upper)) = pointBounds34598 := by
 decide +kernel
def cuts34599 : List PrefixCut := [⟨64,366807527,366807759⟩]
theorem checked34599 : checkPrefixCuts (2^48) 4538892289 10 Manual.Count131072.C034599.packed 64 cuts34599 = true := by
 decide +kernel
def cuts34600 : List PrefixCut := [⟨1,6015183,6015187⟩,
⟨64,368967396,368967627⟩]
theorem checked34600 : checkPrefixCuts (2^48) 4539023361 10 Manual.Count131072.C034600.packed 64 cuts34600 = true := by
 decide +kernel
def pointBounds34600 : List (Nat × Nat × Nat) := [(4539025408,107037884462258,107038268854001)]
theorem point_links_checked34600 : (cuts34600.take 1).map (fun c => (4539023361-1+2*2^10*c.k,107037878447075+c.lower,107038262838814+c.upper)) = pointBounds34600 := by
 decide +kernel
def cuts34601 : List PrefixCut := [⟨7,40926815,40926841⟩,
⟨64,363499867,363500098⟩]
theorem checked34601 : checkPrefixCuts (2^48) 4539154433 10 Manual.Count131072.C034601.packed 64 cuts34601 = true := by
 decide +kernel
def pointBounds34601 : List (Nat × Nat × Nat) := [(4539168768,107038288341286,107038672733282)]
theorem point_links_checked34601 : (cuts34601.take 1).map (fun c => (4539154433-1+2*2^10*c.k,107038247414471+c.lower,107038631806441+c.upper)) = pointBounds34601 := by
 decide +kernel
def cuts34602 : List PrefixCut := [⟨13,75712318,75712368⟩,
⟨64,362001233,362001463⟩]
theorem checked34602 : checkPrefixCuts (2^48) 4539285505 10 Manual.Count131072.C034602.packed 64 cuts34602 = true := by
 decide +kernel
def pointBounds34602 : List (Nat × Nat × Nat) := [(4539312128,107038686626656,107039071018907)]
theorem point_links_checked34602 : (cuts34602.take 1).map (fun c => (4539285505-1+2*2^10*c.k,107038610914338+c.lower,107038995306539+c.upper)) = pointBounds34602 := by
 decide +kernel
def cuts34603 : List PrefixCut := [⟨19,108511517,108511582⟩,
⟨64,370857570,370857799⟩]
theorem checked34603 : checkPrefixCuts (2^48) 4539416577 10 Manual.Count131072.C034603.packed 64 cuts34603 = true := by
 decide +kernel
def pointBounds34603 : List (Nat × Nat × Nat) := [(4539455488,107039081427088,107039465819584)]
theorem point_links_checked34603 : (cuts34603.take 1).map (fun c => (4539416577-1+2*2^10*c.k,107038972915571+c.lower,107039357308002+c.upper)) = pointBounds34603 := by
 decide +kernel
def cuts34604 : List PrefixCut := [⟨25,148191253,148191342⟩,
⟨64,372521011,372521239⟩]
theorem checked34604 : checkPrefixCuts (2^48) 4539547649 10 Manual.Count131072.C034604.packed 64 cuts34604 = true := by
 decide +kernel
def pointBounds34604 : List (Nat × Nat × Nat) := [(4539598848,107039491964394,107039876357143)]
theorem point_links_checked34604 : (cuts34604.take 1).map (fun c => (4539547649-1+2*2^10*c.k,107039343773141+c.lower,107039728165801+c.upper)) = pointBounds34604 := by
 decide +kernel
def cuts34605 : List PrefixCut := [⟨31,171995851,171995960⟩,
⟨64,359489694,359489921⟩]
theorem checked34605 : checkPrefixCuts (2^48) 4539678721 10 Manual.Count131072.C034605.packed 64 cuts34605 = true := by
 decide +kernel
def pointBounds34605 : List (Nat × Nat × Nat) := [(4539742208,107039888290003,107040272683000)]
theorem point_links_checked34605 : (cuts34605.take 1).map (fun c => (4539678721-1+2*2^10*c.k,107039716294152+c.lower,107040100687040+c.upper)) = pointBounds34605 := by
 decide +kernel
def cuts34606 : List PrefixCut := [⟨37,212849289,212849424⟩,
⟨64,363509424,363509655⟩]
theorem checked34606 : checkPrefixCuts (2^48) 4539809793 10 Manual.Count131072.C034606.packed 64 cuts34606 = true := by
 decide +kernel
def pointBounds34606 : List (Nat × Nat × Nat) := [(4539885568,107040288633135,107040673026385)]
theorem point_links_checked34606 : (cuts34606.take 1).map (fun c => (4539809793-1+2*2^10*c.k,107040075783846+c.lower,107040460176961+c.upper)) = pointBounds34606 := by
 decide +kernel
def cuts34607 : List PrefixCut := [⟨43,244462393,244462547⟩,
⟨64,364986863,364987094⟩]
theorem checked34607 : checkPrefixCuts (2^48) 4539940865 10 Manual.Count131072.C034607.packed 64 cuts34607 = true := by
 decide +kernel
def pointBounds34607 : List (Nat × Nat × Nat) := [(4540028928,107040683755663,107041068149163)]
theorem point_links_checked34607 : (cuts34607.take 1).map (fun c => (4539940865-1+2*2^10*c.k,107040439293270+c.lower,107040823686616+c.upper)) = pointBounds34607 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S4.B000143
