import PlattAssemblyKernel
import PlattCertificates.Count131072.C025568
import PlattCertificates.Count131072.C025569
import PlattCertificates.Count131072.C025570
import PlattCertificates.Count131072.C025571
import PlattCertificates.Count131072.C025572
import PlattCertificates.Count131072.C025573
import PlattCertificates.Count131072.C025574
import PlattCertificates.Count131072.C025575
import PlattCertificates.Count131072.C025576
import PlattCertificates.Count131072.C025577
import PlattCertificates.Count131072.C025578
import PlattCertificates.Count131072.C025579
import PlattCertificates.Count131072.C025580
import PlattCertificates.Count131072.C025581
import PlattCertificates.Count131072.C025582
import PlattCertificates.Count131072.C025583
import PlattCertificates.Count131072.C025584
import PlattCertificates.Count131072.C025585
import PlattCertificates.Count131072.C025586
import PlattCertificates.Count131072.C025587
import PlattCertificates.Count131072.C025588
import PlattCertificates.Count131072.C025589
import PlattCertificates.Count131072.C025590
import PlattCertificates.Count131072.C025591
import PlattCertificates.Count131072.C025592
import PlattCertificates.Count131072.C025593
import PlattCertificates.Count131072.C025594
import PlattCertificates.Count131072.C025595
import PlattCertificates.Count131072.C025596
import PlattCertificates.Count131072.C025597
import PlattCertificates.Count131072.C025598
import PlattCertificates.Count131072.C025599
namespace ChenEffective.PlattWindow.Assembly.Prefix.S3.B000174
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts25568 : List PrefixCut := [⟨27,105117008,105117065⟩,
⟨128,495124517,495124795⟩]
theorem checked25568 : checkPrefixCuts (2^48) 3355181057 9 Manual.Count131072.C025568.packed 128 cuts25568 = true := by
 decide +kernel
def pointBounds25568 : List (Nat × Nat × Nat) := [(3355208704,103186226619779,103186608797864)]
theorem point_links_checked25568 : (cuts25568.take 1).map (fun c => (3355181057-1+2*2^9*c.k,103186121502771+c.lower,103186503680799+c.upper)) = pointBounds25568 := by
 decide +kernel
def cuts25569 : List PrefixCut := [⟨2,7466149,7466153⟩,
⟨105,415664997,415665225⟩,
⟨128,504165097,504165377⟩]
theorem checked25569 : checkPrefixCuts (2^48) 3355312129 9 Manual.Count131072.C025569.packed 128 cuts25569 = true := by
 decide +kernel
def pointBounds25569 : List (Nat × Nat × Nat) := [(3355314176,103186624093437,103187006271747),(3355419648,103187032292285,103187414470819)]
theorem point_links_checked25569 : (cuts25569.take 2).map (fun c => (3355312129-1+2*2^9*c.k,103186616627288+c.lower,103186998805594+c.upper)) = pointBounds25569 := by
 decide +kernel
def cuts25570 : List PrefixCut := [⟨80,312975015,312975185⟩,
⟨128,500957702,500957972⟩]
theorem checked25570 : checkPrefixCuts (2^48) 3355443201 9 Manual.Count131072.C025570.packed 128 cuts25570 = true := by
 decide +kernel
def pointBounds25570 : List (Nat × Nat × Nat) := [(3355525120,103187433767400,103187815946156)]
theorem point_links_checked25570 : (cuts25570.take 1).map (fun c => (3355443201-1+2*2^9*c.k,103187120792385+c.lower,103187502970971+c.upper)) = pointBounds25570 := by
 decide +kernel
def cuts25571 : List PrefixCut := [⟨55,213899311,213899426⟩,
⟨128,501860856,501861127⟩]
theorem checked25571 : checkPrefixCuts (2^48) 3355574273 9 Manual.Count131072.C025571.packed 128 cuts25571 = true := by
 decide +kernel
def pointBounds25571 : List (Nat × Nat × Nat) := [(3355630592,103187835649398,103188217828369)]
theorem point_links_checked25571 : (cuts25571.take 1).map (fun c => (3355574273-1+2*2^9*c.k,103187621750087+c.lower,103188003928943+c.upper)) = pointBounds25571 := by
 decide +kernel
def cuts25572 : List PrefixCut := [⟨30,118772832,118772897⟩,
⟨128,502092897,502093170⟩]
theorem checked25572 : checkPrefixCuts (2^48) 3355705345 9 Manual.Count131072.C025572.packed 128 cuts25572 = true := by
 decide +kernel
def pointBounds25572 : List (Nat × Nat × Nat) := [(3355736064,103188242383775,103188624562967)]
theorem point_links_checked25572 : (cuts25572.take 1).map (fun c => (3355705345-1+2*2^9*c.k,103188123610943+c.lower,103188505790070+c.upper)) = pointBounds25572 := by
 decide +kernel
def cuts25573 : List PrefixCut := [⟨5,20549661,20549672⟩,
⟨108,425832631,425832867⟩,
⟨128,498970066,498970343⟩]
theorem checked25573 : checkPrefixCuts (2^48) 3355836417 9 Manual.Count131072.C025573.packed 128 cuts25573 = true := by
 decide +kernel
def pointBounds25573 : List (Nat × Nat × Nat) := [(3355841536,103188646253501,103189028432912),(3355947008,103189051536471,103189433716107)]
theorem point_links_checked25573 : (cuts25573.take 2).map (fun c => (3355836417-1+2*2^9*c.k,103188625703840+c.lower,103189007883240+c.upper)) = pointBounds25573 := by
 decide +kernel
def cuts25574 : List PrefixCut := [⟨83,324919688,324919869⟩,
⟨128,502473025,502473301⟩]
theorem checked25574 : checkPrefixCuts (2^48) 3355967489 9 Manual.Count131072.C025574.packed 128 cuts25574 = true := by
 decide +kernel
def pointBounds25574 : List (Nat × Nat × Nat) := [(3356052480,103189449593594,103189831773452)]
theorem point_links_checked25574 : (cuts25574.take 1).map (fun c => (3355967489-1+2*2^9*c.k,103189124673906+c.lower,103189506853583+c.upper)) = pointBounds25574 := by
 decide +kernel
def cuts25575 : List PrefixCut := [⟨58,220239824,220239945⟩,
⟨128,489369980,489370256⟩]
theorem checked25575 : checkPrefixCuts (2^48) 3356098561 9 Manual.Count131072.C025575.packed 128 cuts25575 = true := by
 decide +kernel
def pointBounds25575 : List (Nat × Nat × Nat) := [(3356157952,103189847386755,103190229566829)]
theorem point_links_checked25575 : (cuts25575.take 1).map (fun c => (3356098561-1+2*2^9*c.k,103189627146931+c.lower,103190009326884+c.upper)) = pointBounds25575 := by
 decide +kernel
def cuts25576 : List PrefixCut := [⟨33,125463501,125463571⟩,
⟨128,496311705,496311982⟩]
theorem checked25576 : checkPrefixCuts (2^48) 3356229633 9 Manual.Count131072.C025576.packed 128 cuts25576 = true := by
 decide +kernel
def pointBounds25576 : List (Nat × Nat × Nat) := [(3356263424,103190241980412,103190624160711)]
theorem point_links_checked25576 : (cuts25576.take 1).map (fun c => (3356229633-1+2*2^9*c.k,103190116516911+c.lower,103190498697140+c.upper)) = pointBounds25576 := by
 decide +kernel
def cuts25577 : List PrefixCut := [⟨8,32538853,32538872⟩,
⟨111,428365560,428365804⟩,
⟨128,493189393,493189674⟩]
theorem checked25577 : checkPrefixCuts (2^48) 3356360705 9 Manual.Count131072.C025577.packed 128 cuts25577 = true := by
 decide +kernel
def pointBounds25577 : List (Nat × Nat × Nat) := [(3356368896,103190645367469,103191027547994),(3356474368,103191041194176,103191423374926)]
theorem point_links_checked25577 : (cuts25577.take 2).map (fun c => (3356360705-1+2*2^9*c.k,103190612828616+c.lower,103190995009122+c.upper)) = pointBounds25577 := by
 decide +kernel
def cuts25578 : List PrefixCut := [⟨86,334093279,334093467⟩,
⟨128,499207909,499208189⟩]
theorem checked25578 : checkPrefixCuts (2^48) 3356491777 9 Manual.Count131072.C025578.packed 128 cuts25578 = true := by
 decide +kernel
def pointBounds25578 : List (Nat × Nat × Nat) := [(3356579840,103191440111288,103191822292263)]
theorem point_links_checked25578 : (cuts25578.take 1).map (fun c => (3356491777-1+2*2^9*c.k,103191106018009+c.lower,103191488198796+c.upper)) = pointBounds25578 := by
 decide +kernel
def cuts25579 : List PrefixCut := [⟨61,238988999,238989129⟩,
⟨128,501452515,501452786⟩]
theorem checked25579 : checkPrefixCuts (2^48) 3356622849 9 Manual.Count131072.C025579.packed 128 cuts25579 = true := by
 decide +kernel
def pointBounds25579 : List (Nat × Nat × Nat) := [(3356685312,103191844214917,103192226396114)]
theorem point_links_checked25579 : (cuts25579.take 1).map (fun c => (3356622849-1+2*2^9*c.k,103191605225918+c.lower,103191987406985+c.upper)) = pointBounds25579 := by
 decide +kernel
def cuts25580 : List PrefixCut := [⟨36,140034250,140034328⟩,
⟨128,498581996,498582274⟩]
theorem checked25580 : checkPrefixCuts (2^48) 3356753921 9 Manual.Count131072.C025580.packed 128 cuts25580 = true := by
 decide +kernel
def pointBounds25580 : List (Nat × Nat × Nat) := [(3356790784,103192246712683,103192628894099)]
theorem point_links_checked25580 : (cuts25580.take 1).map (fun c => (3356753921-1+2*2^9*c.k,103192106678433+c.lower,103192488859771+c.upper)) = pointBounds25580 := by
 decide +kernel
def cuts25581 : List PrefixCut := [⟨11,42763442,42763466⟩,
⟨114,450434428,450434674⟩,
⟨128,505354167,505354444⟩]
theorem checked25581 : checkPrefixCuts (2^48) 3356884993 9 Manual.Count131072.C025581.packed 128 cuts25581 = true := by
 decide +kernel
def pointBounds25581 : List (Nat × Nat × Nat) := [(3356896256,103192648023871,103193030205511),(3357001728,103193055694857,103193437876719)]
theorem point_links_checked25581 : (cuts25581.take 2).map (fun c => (3356884993-1+2*2^9*c.k,103192605260429+c.lower,103192987442045+c.upper)) = pointBounds25581 := by
 decide +kernel
def cuts25582 : List PrefixCut := [⟨89,345779295,345779489⟩,
⟨128,499800695,499800974⟩]
theorem checked25582 : checkPrefixCuts (2^48) 3357016065 9 Manual.Count131072.C025582.packed 128 cuts25582 = true := by
 decide +kernel
def pointBounds25582 : List (Nat × Nat × Nat) := [(3357107200,103193456393891,103193838575978)]
theorem point_links_checked25582 : (cuts25582.take 1).map (fun c => (3357016065-1+2*2^9*c.k,103193110614596+c.lower,103193492796489+c.upper)) = pointBounds25582 := by
 decide +kernel
def cuts25583 : List PrefixCut := [⟨64,253959415,253959554⟩,
⟨128,505314817,505315095⟩]
theorem checked25583 : checkPrefixCuts (2^48) 3357147137 9 Manual.Count131072.C025583.packed 128 cuts25583 = true := by
 decide +kernel
def pointBounds25583 : List (Nat × Nat × Nat) := [(3357212672,103193864374706,103194246557017)]
theorem point_links_checked25583 : (cuts25583.take 1).map (fun c => (3357147137-1+2*2^9*c.k,103193610415291+c.lower,103193992597463+c.upper)) = pointBounds25583 := by
 decide +kernel
def cuts25584 : List PrefixCut := [⟨39,153342827,153342913⟩,
⟨128,497581923,497582200⟩]
theorem checked25584 : checkPrefixCuts (2^48) 3357278209 9 Manual.Count131072.C025584.packed 128 cuts25584 = true := by
 decide +kernel
def pointBounds25584 : List (Nat × Nat × Nat) := [(3357318144,103194269072935,103194651255471)]
theorem point_links_checked25584 : (cuts25584.take 1).map (fun c => (3357278209-1+2*2^9*c.k,103194115730108+c.lower,103194497912558+c.upper)) = pointBounds25584 := by
 decide +kernel
def cuts25585 : List PrefixCut := [⟨14,55164583,55164612⟩,
⟨117,451034625,451034880⟩,
⟨128,495382706,495382984⟩]
theorem checked25585 : checkPrefixCuts (2^48) 3357409281 9 Manual.Count131072.C025585.packed 128 cuts25585 = true := by
 decide +kernel
def pointBounds25585 : List (Nat × Nat × Nat) := [(3357423616,103194668476614,103195050659370),(3357529088,103195064346656,103195446529638)]
theorem point_links_checked25585 : (cuts25585.take 2).map (fun c => (3357409281-1+2*2^9*c.k,103194613312031+c.lower,103194995494758+c.upper)) = pointBounds25585 := by
 decide +kernel
def cuts25586 : List PrefixCut := [⟨92,362156372,362156579⟩,
⟨128,502153888,502154174⟩]
theorem checked25586 : checkPrefixCuts (2^48) 3357540353 9 Manual.Count131072.C025586.packed 128 cuts25586 = true := by
 decide +kernel
def pointBounds25586 : List (Nat × Nat × Nat) := [(3357634560,103195470851109,103195853034321)]
theorem point_links_checked25586 : (cuts25586.take 1).map (fun c => (3357540353-1+2*2^9*c.k,103195108694737+c.lower,103195490877742+c.upper)) = pointBounds25586 := by
 decide +kernel
def cuts25587 : List PrefixCut := [⟨67,261464285,261464428⟩,
⟨128,504481348,504481626⟩]
theorem checked25587 : checkPrefixCuts (2^48) 3357671425 9 Manual.Count131072.C025587.packed 128 cuts25587 = true := by
 decide +kernel
def pointBounds25587 : List (Nat × Nat × Nat) := [(3357740032,103195872312910,103196254496344)]
theorem point_links_checked25587 : (cuts25587.take 1).map (fun c => (3357671425-1+2*2^9*c.k,103195610848625+c.lower,103195993031916+c.upper)) = pointBounds25587 := by
 decide +kernel
def cuts25588 : List PrefixCut := [⟨42,166563408,166563506⟩,
⟨128,506557307,506557594⟩]
theorem checked25588 : checkPrefixCuts (2^48) 3357802497 9 Manual.Count131072.C025588.packed 128 cuts25588 = true := by
 decide +kernel
def pointBounds25588 : List (Nat × Nat × Nat) := [(3357845504,103196281893381,103196664077048)]
theorem point_links_checked25588 : (cuts25588.take 1).map (fun c => (3357802497-1+2*2^9*c.k,103196115329973+c.lower,103196497513542+c.upper)) = pointBounds25588 := by
 decide +kernel
def cuts25589 : List PrefixCut := [⟨17,66388312,66388349⟩,
⟨120,464124160,464124421⟩,
⟨128,493964320,493964597⟩]
theorem checked25589 : checkPrefixCuts (2^48) 3357933569 9 Manual.Count131072.C025589.packed 128 cuts25589 = true := by
 decide +kernel
def pointBounds25589 : List (Nat × Nat × Nat) := [(3357950976,103196688275592,103197070459485),(3358056448,103197086011440,103197468195557)]
theorem point_links_checked25589 : (cuts25589.take 2).map (fun c => (3357933569-1+2*2^9*c.k,103196621887280+c.lower,103197004071136+c.upper)) = pointBounds25589 := by
 decide +kernel
def cuts25590 : List PrefixCut := [⟨95,370230091,370230294⟩,
⟨128,499644649,499644925⟩]
theorem checked25590 : checkPrefixCuts (2^48) 3358064641 9 Manual.Count131072.C025590.packed 128 cuts25590 = true := by
 decide +kernel
def pointBounds25590 : List (Nat × Nat × Nat) := [(3358161920,103197486081691,103197868266027)]
theorem point_links_checked25590 : (cuts25590.take 1).map (fun c => (3358064641-1+2*2^9*c.k,103197115851600+c.lower,103197498035733+c.upper)) = pointBounds25590 := by
 decide +kernel
def cuts25591 : List PrefixCut := [⟨70,273492961,273493112⟩,
⟨128,499038535,499038812⟩]
theorem checked25591 : checkPrefixCuts (2^48) 3358195713 9 Manual.Count131072.C025591.packed 128 cuts25591 = true := by
 decide +kernel
def pointBounds25591 : List (Nat × Nat × Nat) := [(3358267392,103197888989210,103198271173770)]
theorem point_links_checked25591 : (cuts25591.take 1).map (fun c => (3358195713-1+2*2^9*c.k,103197615496249+c.lower,103197997680658+c.upper)) = pointBounds25591 := by
 decide +kernel
def cuts25592 : List PrefixCut := [⟨45,175589205,175589306⟩,
⟨128,499354263,499354545⟩]
theorem checked25592 : checkPrefixCuts (2^48) 3358326785 9 Manual.Count131072.C025592.packed 128 cuts25592 = true := by
 decide +kernel
def pointBounds25592 : List (Nat × Nat × Nat) := [(3358372864,103198290123989,103198672308776)]
theorem point_links_checked25592 : (cuts25592.take 1).map (fun c => (3358326785-1+2*2^9*c.k,103198114534784+c.lower,103198496719470+c.upper)) = pointBounds25592 := by
 decide +kernel
def cuts25593 : List PrefixCut := [⟨20,76938041,76938086⟩,
⟨123,479388470,479388740⟩,
⟨128,497490901,497491181⟩]
theorem checked25593 : checkPrefixCuts (2^48) 3358457857 9 Manual.Count131072.C025593.packed 128 cuts25593 = true := by
 decide +kernel
def pointBounds25593 : List (Nat × Nat × Nat) := [(3358478336,103198690827088,103199073012101),(3358583808,103199093277517,103199475462755)]
theorem point_links_checked25593 : (cuts25593.take 2).map (fun c => (3358457857-1+2*2^9*c.k,103198613889047+c.lower,103198996074015+c.upper)) = pointBounds25593 := by
 decide +kernel
def cuts25594 : List PrefixCut := [⟨98,381737354,381737570⟩,
⟨128,498644769,498645049⟩]
theorem checked25594 : checkPrefixCuts (2^48) 3358588929 9 Manual.Count131072.C025594.packed 128 cuts25594 = true := by
 decide +kernel
def pointBounds25594 : List (Nat × Nat × Nat) := [(3358689280,103199493117302,103199875302766)]
theorem point_links_checked25594 : (cuts25594.take 1).map (fun c => (3358588929-1+2*2^9*c.k,103199111379948+c.lower,103199493565196+c.upper)) = pointBounds25594 := by
 decide +kernel
def cuts25595 : List PrefixCut := [⟨73,285266359,285266515⟩,
⟨128,500133786,500134062⟩]
theorem checked25595 : checkPrefixCuts (2^48) 3358720001 9 Manual.Count131072.C025595.packed 128 cuts25595 = true := by
 decide +kernel
def pointBounds25595 : List (Nat × Nat × Nat) := [(3358794752,103199895291076,103200277476760)]
theorem point_links_checked25595 : (cuts25595.take 1).map (fun c => (3358720001-1+2*2^9*c.k,103199610024717+c.lower,103199992210245+c.upper)) = pointBounds25595 := by
 decide +kernel
def cuts25596 : List PrefixCut := [⟨48,187880345,187880449⟩,
⟨128,496343349,496343628⟩]
theorem checked25596 : checkPrefixCuts (2^48) 3358851073 9 Manual.Count131072.C025596.packed 128 cuts25596 = true := by
 decide +kernel
def pointBounds25596 : List (Nat × Nat × Nat) := [(3358900224,103200298038848,103200680224756)]
theorem point_links_checked25596 : (cuts25596.take 1).map (fun c => (3358851073-1+2*2^9*c.k,103200110158503+c.lower,103200492344307+c.upper)) = pointBounds25596 := by
 decide +kernel
def cuts25597 : List PrefixCut := [⟨23,92177117,92177169⟩,
⟨126,492218131,492218403⟩,
⟨128,499927218,499927495⟩]
theorem checked25597 : checkPrefixCuts (2^48) 3358982145 9 Manual.Count131072.C025597.packed 128 cuts25597 = true := by
 decide +kernel
def pointBounds25597 : List (Nat × Nat × Nat) := [(3359005696,103200698678969,103201080865104),(3359111168,103201098719983,103201480906338)]
theorem point_links_checked25597 : (cuts25597.take 2).map (fun c => (3358982145-1+2*2^9*c.k,103200606501852+c.lower,103200988687935+c.upper)) = pointBounds25597 := by
 decide +kernel
def cuts25598 : List PrefixCut := [⟨101,393241136,393241359⟩,
⟨128,504432440,504432719⟩]
theorem checked25598 : checkPrefixCuts (2^48) 3359113217 9 Manual.Count131072.C025598.packed 128 cuts25598 = true := by
 decide +kernel
def pointBounds25598 : List (Nat × Nat × Nat) := [(3359216640,103201499670206,103201881856789)]
theorem point_links_checked25598 : (cuts25598.take 1).map (fun c => (3359113217-1+2*2^9*c.k,103201106429070+c.lower,103201488615430+c.upper)) = pointBounds25598 := by
 decide +kernel
def cuts25599 : List PrefixCut := [⟨76,292427686,292427845⟩,
⟨128,494274248,494274521⟩]
theorem checked25599 : checkPrefixCuts (2^48) 3359244289 9 Manual.Count131072.C025599.packed 128 cuts25599 = true := by
 decide +kernel
def pointBounds25599 : List (Nat × Nat × Nat) := [(3359322112,103201903289196,103202285475994)]
theorem point_links_checked25599 : (cuts25599.take 1).map (fun c => (3359244289-1+2*2^9*c.k,103201610861510+c.lower,103201993048149+c.upper)) = pointBounds25599 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S3.B000174
