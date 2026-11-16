import PlattAssemblyKernel
import PlattCertificates.Count131072.C019568
import PlattCertificates.Count131072.C019569
import PlattCertificates.Count131072.C019570
import PlattCertificates.Count131072.C019571
import PlattCertificates.Count131072.C019572
import PlattCertificates.Count131072.C019573
import PlattCertificates.Count131072.C019574
import PlattCertificates.Count131072.C019575
import PlattCertificates.Count131072.C019576
import PlattCertificates.Count131072.C019577
import PlattCertificates.Count131072.C019578
import PlattCertificates.Count131072.C019579
import PlattCertificates.Count131072.C019580
import PlattCertificates.Count131072.C019581
import PlattCertificates.Count131072.C019582
import PlattCertificates.Count131072.C019583
import PlattCertificates.Count131072.C019584
import PlattCertificates.Count131072.C019585
import PlattCertificates.Count131072.C019586
import PlattCertificates.Count131072.C019587
import PlattCertificates.Count131072.C019588
import PlattCertificates.Count131072.C019589
import PlattCertificates.Count131072.C019590
import PlattCertificates.Count131072.C019591
import PlattCertificates.Count131072.C019592
import PlattCertificates.Count131072.C019593
import PlattCertificates.Count131072.C019594
import PlattCertificates.Count131072.C019595
import PlattCertificates.Count131072.C019596
import PlattCertificates.Count131072.C019597
import PlattCertificates.Count131072.C019598
import PlattCertificates.Count131072.C019599
namespace ChenEffective.PlattWindow.Assembly.Prefix.S2.B000299
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts19568 : List PrefixCut := [⟨67,349216117,349216325⟩,
⟨128,669715341,669715737⟩]
theorem checked19568 : checkPrefixCuts (2^48) 2568749057 9 Manual.Count131072.C019568.packed 128 cuts19568 = true := by
 decide +kernel
def pointBounds19568 : List (Nat × Nat × Nat) := [(2568817664,99738100544240,99738480747179)]
theorem point_links_checked19568 : (cuts19568.take 1).map (fun c => (2568749057-1+2*2^9*c.k,99737751328123+c.lower,99738131530854+c.upper)) = pointBounds19568 := by
 decide +kernel
def cuts19569 : List PrefixCut := [⟨18,94121187,94121243⟩,
⟨97,499305693,499305988⟩,
⟨128,658833990,658834381⟩]
theorem checked19569 : checkPrefixCuts (2^48) 2568880129 9 Manual.Count131072.C019569.packed 128 cuts19569 = true := by
 decide +kernel
def pointBounds19569 : List (Nat × Nat × Nat) := [(2568898560,99738515164651,99738895367834),(2568979456,99738920349157,99739300552579)]
theorem point_links_checked19569 : (cuts19569.take 2).map (fun c => (2568880129-1+2*2^9*c.k,99738421043464+c.lower,99738801246591+c.upper)) = pointBounds19569 := by
 decide +kernel
def cuts19570 : List PrefixCut := [⟨48,249368592,249368741⟩,
⟨127,663840363,663840754⟩,
⟨128,668222759,668223152⟩]
theorem checked19570 : checkPrefixCuts (2^48) 2569011201 9 Manual.Count131072.C019570.packed 128 cuts19570 = true := by
 decide +kernel
def pointBounds19570 : List (Nat × Nat × Nat) := [(2569060352,99739329246046,99739709449713),(2569141248,99739743717817,99740123921726)]
theorem point_links_checked19570 : (cuts19570.take 2).map (fun c => (2569011201-1+2*2^9*c.k,99739079877454+c.lower,99739460080972+c.upper)) = pointBounds19570 := by
 decide +kernel
def cuts19571 : List PrefixCut := [⟨78,404927021,404927268⟩,
⟨128,662929922,662930321⟩]
theorem checked19571 : checkPrefixCuts (2^48) 2569142273 9 Manual.Count131072.C019571.packed 128 cuts19571 = true := by
 decide +kernel
def pointBounds19571 : List (Nat × Nat × Nat) := [(2569222144,99740153027234,99740533231392)]
theorem point_links_checked19571 : (cuts19571.take 1).map (fun c => (2569142273-1+2*2^9*c.k,99739748100213+c.lower,99740128304124+c.upper)) = pointBounds19571 := by
 decide +kernel
def cuts19572 : List PrefixCut := [⟨29,151622239,151622327⟩,
⟨108,559262578,559262910⟩,
⟨128,664539294,664539690⟩]
theorem checked19572 : checkPrefixCuts (2^48) 2569273345 9 Manual.Count131072.C019572.packed 128 cuts19572 = true := by
 decide +kernel
def pointBounds19572 : List (Nat × Nat × Nat) := [(2569303040,99740562652374,99740942856772),(2569383936,99740970292713,99741350497355)]
theorem point_links_checked19572 : (cuts19572.take 2).map (fun c => (2569273345-1+2*2^9*c.k,99740411030135+c.lower,99740791234445+c.upper)) = pointBounds19572 := by
 decide +kernel
def cuts19573 : List PrefixCut := [⟨59,309580967,309581149⟩,
⟨128,664505511,664505901⟩]
theorem checked19573 : checkPrefixCuts (2^48) 2569404417 9 Manual.Count131072.C019573.packed 128 cuts19573 = true := by
 decide +kernel
def pointBounds19573 : List (Nat × Nat × Nat) := [(2569464832,99741385150396,99741765355284)]
theorem point_links_checked19573 : (cuts19573.take 1).map (fun c => (2569404417-1+2*2^9*c.k,99741075569429+c.lower,99741455774135+c.upper)) = pointBounds19573 := by
 decide +kernel
def cuts19574 : List PrefixCut := [⟨10,52361496,52361528⟩,
⟨89,461496942,461497216⟩,
⟨128,660637690,660638084⟩]
theorem checked19574 : checkPrefixCuts (2^48) 2569535489 9 Manual.Count131072.C019574.packed 128 cuts19574 = true := by
 decide +kernel
def pointBounds19574 : List (Nat × Nat × Nat) := [(2569545728,99741792436436,99742172641564),(2569626624,99742201571882,99742581777252)]
theorem point_links_checked19574 : (cuts19574.take 2).map (fun c => (2569535489-1+2*2^9*c.k,99741740074940+c.lower,99742120280036+c.upper)) = pointBounds19574 := by
 decide +kernel
def cuts19575 : List PrefixCut := [⟨40,211296166,211296294⟩,
⟨119,618434170,618434540⟩,
⟨128,665423453,665423850⟩]
theorem checked19575 : checkPrefixCuts (2^48) 2569666561 9 Manual.Count131072.C019575.packed 128 cuts19575 = true := by
 decide +kernel
def pointBounds19575 : List (Nat × Nat × Nat) := [(2569707520,99742612008796,99742992214414),(2569788416,99743019146800,99743399352660)]
theorem point_links_checked19575 : (cuts19575.take 2).map (fun c => (2569666561-1+2*2^9*c.k,99742400712630+c.lower,99742780918120+c.upper)) = pointBounds19575 := by
 decide +kernel
def cuts19576 : List PrefixCut := [⟨70,366488687,366488907⟩,
⟨128,669989732,669990130⟩]
theorem checked19576 : checkPrefixCuts (2^48) 2569797633 9 Manual.Count131072.C019576.packed 128 cuts19576 = true := by
 decide +kernel
def pointBounds19576 : List (Nat × Nat × Nat) := [(2569869312,99743432624770,99743812830877)]
theorem point_links_checked19576 : (cuts19576.take 1).map (fun c => (2569797633-1+2*2^9*c.k,99743066136083+c.lower,99743446341970+c.upper)) = pointBounds19576 := by
 decide +kernel
def cuts19577 : List PrefixCut := [⟨21,113797387,113797456⟩,
⟨100,514435050,514435355⟩,
⟨128,656922350,656922741⟩]
theorem checked19577 : checkPrefixCuts (2^48) 2569928705 9 Manual.Count131072.C019577.packed 128 cuts19577 = true := by
 decide +kernel
def pointBounds19577 : List (Nat × Nat × Nat) := [(2569950208,99743849923202,99744230129556),(2570031104,99744250560865,99744630767455)]
theorem point_links_checked19577 : (cuts19577.take 2).map (fun c => (2569928705-1+2*2^9*c.k,99743736125815+c.lower,99744116332100+c.upper)) = pointBounds19577 := by
 decide +kernel
def cuts19578 : List PrefixCut := [⟨51,265585092,265585248⟩,
⟨128,660502888,660503275⟩]
theorem checked19578 : checkPrefixCuts (2^48) 2570059777 9 Manual.Count131072.C019578.packed 128 cuts19578 = true := by
 decide +kernel
def pointBounds19578 : List (Nat × Nat × Nat) := [(2570112000,99744658633257,99745038840089)]
theorem point_links_checked19578 : (cuts19578.take 1).map (fun c => (2570059777-1+2*2^9*c.k,99744393048165+c.lower,99744773254841+c.upper)) = pointBounds19578 := by
 decide +kernel
def cuts19579 : List PrefixCut := [⟨2,11061028,11061034⟩,
⟨81,416808054,416808305⟩,
⟨128,654117547,654117939⟩]
theorem checked19579 : checkPrefixCuts (2^48) 2570190849 9 Manual.Count131072.C019579.packed 128 cuts19579 = true := by
 decide +kernel
def pointBounds19579 : List (Nat × Nat × Nat) := [(2570192896,99745064612081,99745444819150),(2570273792,99745470359107,99745850566421)]
theorem point_links_checked19579 : (cuts19579.take 2).map (fun c => (2570190849-1+2*2^9*c.k,99745053551053+c.lower,99745433758116+c.upper)) = pointBounds19579 := by
 decide +kernel
def cuts19580 : List PrefixCut := [⟨32,170943368,170943466⟩,
⟨111,578088350,578088688⟩,
⟨128,666677395,666677785⟩]
theorem checked19580 : checkPrefixCuts (2^48) 2570321921 9 Manual.Count131072.C019580.packed 128 cuts19580 = true := by
 decide +kernel
def pointBounds19580 : List (Nat × Nat × Nat) := [(2570354688,99745878611968,99746258819521),(2570435584,99746285756950,99746665964743)]
theorem point_links_checked19580 : (cuts19580.take 2).map (fun c => (2570321921-1+2*2^9*c.k,99745707668600+c.lower,99746087876055+c.upper)) = pointBounds19580 := by
 decide +kernel
def cuts19581 : List PrefixCut := [⟨62,319747774,319747963⟩,
⟨128,659744815,659745202⟩]
theorem checked19581 : checkPrefixCuts (2^48) 2570452993 9 Manual.Count131072.C019581.packed 128 cuts19581 = true := by
 decide +kernel
def pointBounds19581 : List (Nat × Nat × Nat) := [(2570516480,99746694093769,99747074301803)]
theorem point_links_checked19581 : (cuts19581.take 1).map (fun c => (2570452993-1+2*2^9*c.k,99746374345995+c.lower,99746754553840+c.upper)) = pointBounds19581 := by
 decide +kernel
def cuts19582 : List PrefixCut := [⟨13,67888847,67888887⟩,
⟨92,481346244,481346530⟩,
⟨128,667813888,667814284⟩]
theorem checked19582 : checkPrefixCuts (2^48) 2570584065 9 Manual.Count131072.C019582.packed 128 cuts19582 = true := by
 decide +kernel
def pointBounds19582 : List (Nat × Nat × Nat) := [(2570597376,99747101979657,99747482187929),(2570678272,99747515437054,99747895645572)]
theorem point_links_checked19582 : (cuts19582.take 2).map (fun c => (2570584065-1+2*2^9*c.k,99747034090810+c.lower,99747414299042+c.upper)) = pointBounds19582 := by
 decide +kernel
def cuts19583 : List PrefixCut := [⟨43,229823499,229823638⟩,
⟨122,638218392,638218773⟩,
⟨128,668984346,668984746⟩]
theorem checked19583 : checkPrefixCuts (2^48) 2570715137 9 Manual.Count131072.C019583.packed 128 cuts19583 = true := by
 decide +kernel
def pointBounds19583 : List (Nat × Nat × Nat) := [(2570759168,99747931728197,99748311936964),(2570840064,99748340123090,99748720332099)]
theorem point_links_checked19583 : (cuts19583.take 2).map (fun c => (2570715137-1+2*2^9*c.k,99747701904698+c.lower,99748082113326+c.upper)) = pointBounds19583 := by
 decide +kernel
def cuts19584 : List PrefixCut := [⟨73,378601434,378601660⟩,
⟨128,662490528,662490924⟩]
theorem checked19584 : checkPrefixCuts (2^48) 2570846209 9 Manual.Count131072.C019584.packed 128 cuts19584 = true := by
 decide +kernel
def pointBounds19584 : List (Nat × Nat × Nat) := [(2570920960,99748749490478,99749129699732)]
theorem point_links_checked19584 : (cuts19584.take 1).map (fun c => (2570846209-1+2*2^9*c.k,99748370889044+c.lower,99748751098072+c.upper)) = pointBounds19584 := by
 decide +kernel
def cuts19585 : List PrefixCut := [⟨24,125684359,125684432⟩,
⟨103,529552040,529552352⟩,
⟨128,659829233,659829621⟩]
theorem checked19585 : checkPrefixCuts (2^48) 2570977281 9 Manual.Count131072.C019585.packed 128 cuts19585 = true := by
 decide +kernel
def pointBounds19585 : List (Nat × Nat × Nat) := [(2571001856,99749159063931,99749539273428),(2571082752,99749562931612,99749943141348)]
theorem point_links_checked19585 : (cuts19585.take 2).map (fun c => (2570977281-1+2*2^9*c.k,99749033379572+c.lower,99749413588996+c.upper)) = pointBounds19585 := by
 decide +kernel
def cuts19586 : List PrefixCut := [⟨54,274344169,274344333⟩,
⟨128,659904959,659905349⟩]
theorem checked19586 : checkPrefixCuts (2^48) 2571108353 9 Manual.Count131072.C019586.packed 128 cuts19586 = true := by
 decide +kernel
def pointBounds19586 : List (Nat × Nat × Nat) := [(2571163648,99749967552974,99750347762950)]
theorem point_links_checked19586 : (cuts19586.take 1).map (fun c => (2571108353-1+2*2^9*c.k,99749693208805+c.lower,99750073418617+c.upper)) = pointBounds19586 := by
 decide +kernel
def cuts19587 : List PrefixCut := [⟨5,26272897,26272912⟩,
⟨84,433933850,433934107⟩,
⟨128,659214652,659215042⟩]
theorem checked19587 : checkPrefixCuts (2^48) 2571239425 9 Manual.Count131072.C019587.packed 128 cuts19587 = true := by
 decide +kernel
def pointBounds19587 : List (Nat × Nat × Nat) := [(2571244544,99750379386661,99750759596878),(2571325440,99750787047614,99751167258073)]
theorem point_links_checked19587 : (cuts19587.take 2).map (fun c => (2571239425-1+2*2^9*c.k,99750353113764+c.lower,99750733323966+c.upper)) = pointBounds19587 := by
 decide +kernel
def cuts19588 : List PrefixCut := [⟨35,178645518,178645628⟩,
⟨114,585624061,585624407⟩,
⟨128,657648516,657648905⟩]
theorem checked19588 : checkPrefixCuts (2^48) 2571370497 9 Manual.Count131072.C019588.packed 128 cuts19588 = true := by
 decide +kernel
def pointBounds19588 : List (Nat × Nat × Nat) := [(2571406336,99751190973934,99751571184636),(2571487232,99751597952477,99751978163415)]
theorem point_links_checked19588 : (cuts19588.take 2).map (fun c => (2571370497-1+2*2^9*c.k,99751012328416+c.lower,99751392539008+c.upper)) = pointBounds19588 := by
 decide +kernel
def cuts19589 : List PrefixCut := [⟨65,339866815,339867012⟩,
⟨128,662540570,662540961⟩]
theorem checked19589 : checkPrefixCuts (2^48) 2571501569 9 Manual.Count131072.C019589.packed 128 cuts19589 = true := by
 decide +kernel
def pointBounds19589 : List (Nat × Nat × Nat) := [(2571568128,99752009843747,99752390054925)]
theorem point_links_checked19589 : (cuts19589.take 1).map (fun c => (2571501569-1+2*2^9*c.k,99751669976932+c.lower,99752050187913+c.upper)) = pointBounds19589 := by
 decide +kernel
def cuts19590 : List PrefixCut := [⟨16,82308976,82309027⟩,
⟨95,484214279,484214570⟩,
⟨128,657471903,657472295⟩]
theorem checked19590 : checkPrefixCuts (2^48) 2571632641 9 Manual.Count131072.C019590.packed 128 cuts19590 = true := by
 decide +kernel
def pointBounds19590 : List (Nat × Nat × Nat) := [(2571649024,99752414826478,99752795037901),(2571729920,99752816731781,99753196943444)]
theorem point_links_checked19590 : (cuts19590.take 2).map (fun c => (2571632641-1+2*2^9*c.k,99752332517502+c.lower,99752712728874+c.upper)) = pointBounds19590 := by
 decide +kernel
def cuts19591 : List PrefixCut := [⟨46,238704299,238704440⟩,
⟨125,654921623,654922007⟩,
⟨128,670134155,670134548⟩]
theorem checked19591 : checkPrefixCuts (2^48) 2571763713 9 Manual.Count131072.C019591.packed 128 cuts19591 = true := by
 decide +kernel
def pointBounds19591 : List (Nat × Nat × Nat) := [(2571810816,99753228693704,99753608905609),(2571891712,99753644911028,99754025123176)]
theorem point_links_checked19591 : (cuts19591.take 2).map (fun c => (2571763713-1+2*2^9*c.k,99752989989405+c.lower,99753370201169+c.upper)) = pointBounds19591 := by
 decide +kernel
def cuts19592 : List PrefixCut := [⟨76,385998318,385998548⟩,
⟨128,656310615,656311007⟩]
theorem checked19592 : checkPrefixCuts (2^48) 2571894785 9 Manual.Count131072.C019592.packed 128 cuts19592 = true := by
 decide +kernel
def pointBounds19592 : List (Nat × Nat × Nat) := [(2571972608,99754046121878,99754426334265)]
theorem point_links_checked19592 : (cuts19592.take 1).map (fun c => (2571894785-1+2*2^9*c.k,99753660123560+c.lower,99754040335717+c.upper)) = pointBounds19592 := by
 decide +kernel
def cuts19593 : List PrefixCut := [⟨27,138765422,138765505⟩,
⟨106,547283015,547283340⟩,
⟨128,664812932,664813325⟩]
theorem checked19593 : checkPrefixCuts (2^48) 2572025857 9 Manual.Count131072.C019593.packed 128 cuts19593 = true := by
 decide +kernel
def pointBounds19593 : List (Nat × Nat × Nat) := [(2572053504,99754455199597,99754835412229),(2572134400,99754863717190,99755243930064)]
theorem point_links_checked19593 : (cuts19593.take 2).map (fun c => (2572025857-1+2*2^9*c.k,99754316434175+c.lower,99754696646724+c.upper)) = pointBounds19593 := by
 decide +kernel
def cuts19594 : List PrefixCut := [⟨57,292616412,292616586⟩,
⟨128,661824528,661824922⟩]
theorem checked19594 : checkPrefixCuts (2^48) 2572156929 9 Manual.Count131072.C019594.packed 128 cuts19594 = true := by
 decide +kernel
def pointBounds19594 : List (Nat × Nat × Nat) := [(2572215296,99755273863519,99755654076635)]
theorem point_links_checked19594 : (cuts19594.take 1).map (fun c => (2572156929-1+2*2^9*c.k,99754981247107+c.lower,99755361460049+c.upper)) = pointBounds19594 := by
 decide +kernel
def cuts19595 : List PrefixCut := [⟨8,42457178,42457204⟩,
⟨87,450608039,450608304⟩,
⟨128,665839546,665839938⟩]
theorem checked19595 : checkPrefixCuts (2^48) 2572288001 9 Manual.Count131072.C019595.packed 128 cuts19595 = true := by
 decide +kernel
def pointBounds19595 : List (Nat × Nat × Nat) := [(2572296192,99755685528813,99756065742175),(2572377088,99756093679674,99756473893275)]
theorem point_links_checked19595 : (cuts19595.take 2).map (fun c => (2572288001-1+2*2^9*c.k,99755643071635+c.lower,99756023284971+c.upper)) = pointBounds19595 := by
 decide +kernel
def cuts19596 : List PrefixCut := [⟨38,205927485,205927601⟩,
⟨117,613067905,613068266⟩,
⟨128,673574389,673574786⟩]
theorem checked19596 : checkPrefixCuts (2^48) 2572419073 9 Manual.Count131072.C019596.packed 128 cuts19596 = true := by
 decide +kernel
def pointBounds19596 : List (Nat × Nat × Nat) := [(2572457984,99756514838666,99756895052510),(2572538880,99756921979086,99757302193175)]
theorem point_links_checked19596 : (cuts19596.take 2).map (fun c => (2572419073-1+2*2^9*c.k,99756308911181+c.lower,99756689124909+c.upper)) = pointBounds19596 := by
 decide +kernel
def cuts19597 : List PrefixCut := [⟨68,352748322,352748530⟩,
⟨128,658112902,658113293⟩]
theorem checked19597 : checkPrefixCuts (2^48) 2572550145 9 Manual.Count131072.C019597.packed 128 cuts19597 = true := by
 decide +kernel
def pointBounds19597 : List (Nat × Nat × Nat) := [(2572619776,99757335233892,99757715448225)]
theorem point_links_checked19597 : (cuts19597.take 1).map (fun c => (2572550145-1+2*2^9*c.k,99756982485570+c.lower,99757362699695+c.upper)) = pointBounds19597 := by
 decide +kernel
def cuts19598 : List PrefixCut := [⟨19,97045560,97045619⟩,
⟨98,513556590,513556889⟩,
⟨128,664643840,664644228⟩]
theorem checked19598 : checkPrefixCuts (2^48) 2572681217 9 Manual.Count131072.C019598.packed 128 cuts19598 = true := by
 decide +kernel
def pointBounds19598 : List (Nat × Nat × Nat) := [(2572700672,99757737644032,99758117858607),(2572781568,99758154155062,99758534369877)]
theorem point_links_checked19598 : (cuts19598.take 2).map (fun c => (2572681217-1+2*2^9*c.k,99757640598472+c.lower,99758020812988+c.upper)) = pointBounds19598 := by
 decide +kernel
def cuts19599 : List PrefixCut := [⟨49,249765931,249766077⟩,
⟨128,659030367,659030750⟩]
theorem checked19599 : checkPrefixCuts (2^48) 2572812289 9 Manual.Count131072.C019599.packed 128 cuts19599 = true := by
 decide +kernel
def pointBounds19599 : List (Nat × Nat × Nat) := [(2572862464,99758555008243,99758935223293),(2572943360,99758964272679,99759344487966)]
theorem point_links_checked19599 : (cuts19599.take 2).map (fun c => (2572812289-1+2*2^9*c.k,99758305242312+c.lower,99758685457216+c.upper)) = pointBounds19599 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S2.B000299
