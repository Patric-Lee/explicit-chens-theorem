import PlattAssemblyKernel
import PlattCertificates.Count131072.C033584
import PlattCertificates.Count131072.C033585
import PlattCertificates.Count131072.C033586
import PlattCertificates.Count131072.C033587
import PlattCertificates.Count131072.C033588
import PlattCertificates.Count131072.C033589
import PlattCertificates.Count131072.C033590
import PlattCertificates.Count131072.C033591
import PlattCertificates.Count131072.C033592
import PlattCertificates.Count131072.C033593
import PlattCertificates.Count131072.C033594
import PlattCertificates.Count131072.C033595
import PlattCertificates.Count131072.C033596
import PlattCertificates.Count131072.C033597
import PlattCertificates.Count131072.C033598
import PlattCertificates.Count131072.C033599
import PlattCertificates.Count131072.C033600
import PlattCertificates.Count131072.C033601
import PlattCertificates.Count131072.C033602
import PlattCertificates.Count131072.C033603
import PlattCertificates.Count131072.C033604
import PlattCertificates.Count131072.C033605
import PlattCertificates.Count131072.C033606
import PlattCertificates.Count131072.C033607
import PlattCertificates.Count131072.C033608
import PlattCertificates.Count131072.C033609
import PlattCertificates.Count131072.C033610
import PlattCertificates.Count131072.C033611
import PlattCertificates.Count131072.C033612
import PlattCertificates.Count131072.C033613
import PlattCertificates.Count131072.C033614
import PlattCertificates.Count131072.C033615
namespace ChenEffective.PlattWindow.Assembly.Prefix.S4.B000112
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts33584 : List PrefixCut := [⟨64,380055555,380055797⟩]
theorem checked33584 : checkPrefixCuts (2^48) 4405854209 10 Manual.Count131072.C033584.packed 64 cuts33584 = true := by
 decide +kernel
def cuts33585 : List PrefixCut := [⟨1,6069042,6069045⟩,
⟨64,376850039,376850277⟩]
theorem checked33585 : checkPrefixCuts (2^48) 4405985281 10 Manual.Count131072.C033585.packed 64 cuts33585 = true := by
 decide +kernel
def pointBounds33585 : List (Nat × Nat × Nat) := [(4405987328,106661077347489,106661461501775)]
theorem point_links_checked33585 : (cuts33585.take 1).map (fun c => (4405985281-1+2*2^10*c.k,106661071278447+c.lower,106661455432730+c.upper)) = pointBounds33585 := by
 decide +kernel
def cuts33586 : List PrefixCut := [⟨5,26511316,26511332⟩,
⟨64,374155716,374155952⟩]
theorem checked33586 : checkPrefixCuts (2^48) 4406116353 10 Manual.Count131072.C033586.packed 64 cuts33586 = true := by
 decide +kernel
def pointBounds33586 : List (Nat × Nat × Nat) := [(4406126592,106661474639802,106661858794339)]
theorem point_links_checked33586 : (cuts33586.take 1).map (fun c => (4406116353-1+2*2^10*c.k,106661448128486+c.lower,106661832283007+c.upper)) = pointBounds33586 := by
 decide +kernel
def cuts33587 : List PrefixCut := [⟨9,51871152,51871187⟩,
⟨64,378871738,378871980⟩]
theorem checked33587 : checkPrefixCuts (2^48) 4406247425 10 Manual.Count131072.C033587.packed 64 cuts33587 = true := by
 decide +kernel
def pointBounds33587 : List (Nat × Nat × Nat) := [(4406265856,106661874155354,106662258310146)]
theorem point_links_checked33587 : (cuts33587.take 1).map (fun c => (4406247425-1+2*2^10*c.k,106661822284202+c.lower,106662206438959+c.upper)) = pointBounds33587 := by
 decide +kernel
def cuts33588 : List PrefixCut := [⟨13,78634768,78634818⟩,
⟨64,374900089,374900324⟩]
theorem checked33588 : checkPrefixCuts (2^48) 4406378497 10 Manual.Count131072.C033588.packed 64 cuts33588 = true := by
 decide +kernel
def pointBounds33588 : List (Nat × Nat × Nat) := [(4406405120,106662279790708,106662663945757)]
theorem point_links_checked33588 : (cuts33588.take 1).map (fun c => (4406378497-1+2*2^10*c.k,106662201155940+c.lower,106662585310939+c.upper)) = pointBounds33588 := by
 decide +kernel
def cuts33589 : List PrefixCut := [⟨17,100733740,100733806⟩,
⟨64,374825052,374825295⟩]
theorem checked33589 : checkPrefixCuts (2^48) 4406509569 10 Manual.Count131072.C033589.packed 64 cuts33589 = true := by
 decide +kernel
def pointBounds33589 : List (Nat × Nat × Nat) := [(4406544384,106662676789769,106663060945069)]
theorem point_links_checked33589 : (cuts33589.take 1).map (fun c => (4406509569-1+2*2^10*c.k,106662576056029+c.lower,106662960211263+c.upper)) = pointBounds33589 := by
 decide +kernel
def cuts33590 : List PrefixCut := [⟨21,123086842,123086924⟩,
⟨64,379157329,379157570⟩]
theorem checked33590 : checkPrefixCuts (2^48) 4406640641 10 Manual.Count131072.C033590.packed 64 cuts33590 = true := by
 decide +kernel
def pointBounds33590 : List (Nat × Nat × Nat) := [(4406683648,106663073967923,106663458123482)]
theorem point_links_checked33590 : (cuts33590.take 1).map (fun c => (4406640641-1+2*2^10*c.k,106662950881081+c.lower,106663335036558+c.upper)) = pointBounds33590 := by
 decide +kernel
def cuts33591 : List PrefixCut := [⟨25,146141164,146141256⟩,
⟨64,377229858,377230096⟩]
theorem checked33591 : checkPrefixCuts (2^48) 4406771713 10 Manual.Count131072.C033591.packed 64 cuts33591 = true := by
 decide +kernel
def pointBounds33591 : List (Nat × Nat × Nat) := [(4406822912,106663476179574,106663860335384)]
theorem point_links_checked33591 : (cuts33591.take 1).map (fun c => (4406771713-1+2*2^10*c.k,106663330038410+c.lower,106663714194128+c.upper)) = pointBounds33591 := by
 decide +kernel
def cuts33592 : List PrefixCut := [⟨29,168299921,168300028⟩,
⟨64,376132852,376133095⟩]
theorem checked33592 : checkPrefixCuts (2^48) 4406902785 10 Manual.Count131072.C033592.packed 64 cuts33592 = true := by
 decide +kernel
def pointBounds33592 : List (Nat × Nat × Nat) := [(4406962176,106663875568189,106664259724252)]
theorem point_links_checked33592 : (cuts33592.take 1).map (fun c => (4406902785-1+2*2^10*c.k,106663707268268+c.lower,106664091424224+c.upper)) = pointBounds33592 := by
 decide +kernel
def cuts33593 : List PrefixCut := [⟨33,198121563,198121689⟩,
⟨64,380656375,380656618⟩]
theorem checked33593 : checkPrefixCuts (2^48) 4407033857 10 Manual.Count131072.C033593.packed 64 cuts33593 = true := by
 decide +kernel
def pointBounds33593 : List (Nat × Nat × Nat) := [(4407101440,106664281522683,106664665679008)]
theorem point_links_checked33593 : (cuts33593.take 1).map (fun c => (4407033857-1+2*2^10*c.k,106664083401120+c.lower,106664467557319+c.upper)) = pointBounds33593 := by
 decide +kernel
def cuts33594 : List PrefixCut := [⟨37,215040263,215040402⟩,
⟨64,378601254,378601496⟩]
theorem checked33594 : checkPrefixCuts (2^48) 4407164929 10 Manual.Count131072.C033594.packed 64 cuts33594 = true := by
 decide +kernel
def pointBounds33594 : List (Nat × Nat × Nat) := [(4407240704,106664679097758,106665063254339)]
theorem point_links_checked33594 : (cuts33594.take 1).map (fun c => (4407164929-1+2*2^10*c.k,106664464057495+c.lower,106664848213937+c.upper)) = pointBounds33594 := by
 decide +kernel
def cuts33595 : List PrefixCut := [⟨41,240835104,240835256⟩,
⟨64,373225404,373225642⟩]
theorem checked33595 : checkPrefixCuts (2^48) 4407296001 10 Manual.Count131072.C033595.packed 64 cuts33595 = true := by
 decide +kernel
def pointBounds33595 : List (Nat × Nat × Nat) := [(4407379968,106665083493853,106665467650689)]
theorem point_links_checked33595 : (cuts33595.take 1).map (fun c => (4407296001-1+2*2^10*c.k,106664842658749+c.lower,106665226815433+c.upper)) = pointBounds33595 := by
 decide +kernel
def cuts33596 : List PrefixCut := [⟨45,270332466,270332637⟩,
⟨64,381899634,381899878⟩]
theorem checked33596 : checkPrefixCuts (2^48) 4407427073 10 Manual.Count131072.C033596.packed 64 cuts33596 = true := by
 decide +kernel
def pointBounds33596 : List (Nat × Nat × Nat) := [(4407519232,106665486216619,106665870373712)]
theorem point_links_checked33596 : (cuts33596.take 1).map (fun c => (4407427073-1+2*2^10*c.k,106665215884153+c.lower,106665600041075+c.upper)) = pointBounds33596 := by
 decide +kernel
def cuts33597 : List PrefixCut := [⟨49,286991921,286992103⟩,
⟨64,380036211,380036453⟩]
theorem checked33597 : checkPrefixCuts (2^48) 4407558145 10 Manual.Count131072.C033597.packed 64 cuts33597 = true := by
 decide +kernel
def pointBounds33597 : List (Nat × Nat × Nat) := [(4407658496,106665884775708,106666268933056)]
theorem point_links_checked33597 : (cuts33597.take 1).map (fun c => (4407558145-1+2*2^10*c.k,106665597783787+c.lower,106665981940953+c.upper)) = pointBounds33597 := by
 decide +kernel
def cuts33598 : List PrefixCut := [⟨53,313867903,313868100⟩,
⟨64,376895978,376896215⟩]
theorem checked33598 : checkPrefixCuts (2^48) 4407689217 10 Manual.Count131072.C033598.packed 64 cuts33598 = true := by
 decide +kernel
def pointBounds33598 : List (Nat × Nat × Nat) := [(4407797760,106666291687901,106666675845506)]
theorem point_links_checked33598 : (cuts33598.take 1).map (fun c => (4407689217-1+2*2^10*c.k,106665977819998+c.lower,106666361977406+c.upper)) = pointBounds33598 := by
 decide +kernel
def cuts33599 : List PrefixCut := [⟨57,329822554,329822765⟩,
⟨64,371839982,371840220⟩]
theorem checked33599 : checkPrefixCuts (2^48) 4407820289 10 Manual.Count131072.C033599.packed 64 cuts33599 = true := by
 decide +kernel
def pointBounds33599 : List (Nat × Nat × Nat) := [(4407937024,106666684538530,106667068696386)]
theorem point_links_checked33599 : (cuts33599.take 1).map (fun c => (4407820289-1+2*2^10*c.k,106666354715976+c.lower,106666738873621+c.upper)) = pointBounds33599 := by
 decide +kernel
def cuts33600 : List PrefixCut := [⟨61,361867765,361867995⟩,
⟨64,379874680,379874922⟩]
theorem checked33600 : checkPrefixCuts (2^48) 4407951361 10 Manual.Count131072.C033600.packed 64 cuts33600 = true := by
 decide +kernel
def pointBounds33600 : List (Nat × Nat × Nat) := [(4408076288,106667088423723,106667472581836)]
theorem point_links_checked33600 : (cuts33600.take 1).map (fun c => (4407951361-1+2*2^10*c.k,106666726555958+c.lower,106667110713841+c.upper)) = pointBounds33600 := by
 decide +kernel
def cuts33601 : List PrefixCut := [⟨64,380182703,380182946⟩]
theorem checked33601 : checkPrefixCuts (2^48) 4408082433 10 Manual.Count131072.C033601.packed 64 cuts33601 = true := by
 decide +kernel
def cuts33602 : List PrefixCut := [⟨1,6321383,6321387⟩,
⟨64,376659573,376659815⟩]
theorem checked33602 : checkPrefixCuts (2^48) 4408213505 10 Manual.Count131072.C033602.packed 64 cuts33602 = true := by
 decide +kernel
def pointBounds33602 : List (Nat × Nat × Nat) := [(4408215552,106667492934724,106667877093096)]
theorem point_links_checked33602 : (cuts33602.take 1).map (fun c => (4408213505-1+2*2^10*c.k,106667486613341+c.lower,106667870771709+c.upper)) = pointBounds33602 := by
 decide +kernel
def cuts33603 : List PrefixCut := [⟨5,28477278,28477296⟩,
⟨64,377031416,377031658⟩]
theorem checked33603 : checkPrefixCuts (2^48) 4408344577 10 Manual.Count131072.C033603.packed 64 cuts33603 = true := by
 decide +kernel
def pointBounds33603 : List (Nat × Nat × Nat) := [(4408354816,106667891750192,106668275908820)]
theorem point_links_checked33603 : (cuts33603.take 1).map (fun c => (4408344577-1+2*2^10*c.k,106667863272914+c.lower,106668247431524+c.upper)) = pointBounds33603 := by
 decide +kernel
def cuts33604 : List PrefixCut := [⟨9,52611117,52611149⟩,
⟨64,372550887,372551116⟩]
theorem checked33604 : checkPrefixCuts (2^48) 4408475649 10 Manual.Count131072.C033604.packed 64 cuts33604 = true := by
 decide +kernel
def pointBounds33604 : List (Nat × Nat × Nat) := [(4408494080,106668292915447,106668677074331)]
theorem point_links_checked33604 : (cuts33604.take 1).map (fun c => (4408475649-1+2*2^10*c.k,106668240304330+c.lower,106668624463182+c.upper)) = pointBounds33604 := by
 decide +kernel
def cuts33605 : List PrefixCut := [⟨13,73551148,73551197⟩,
⟨64,374135975,374136212⟩]
theorem checked33605 : checkPrefixCuts (2^48) 4408606721 10 Manual.Count131072.C033605.packed 64 cuts33605 = true := by
 decide +kernel
def pointBounds33605 : List (Nat × Nat × Nat) := [(4408633344,106668686406365,106669070565495)]
theorem point_links_checked33605 : (cuts33605.take 1).map (fun c => (4408606721-1+2*2^10*c.k,106668612855217+c.lower,106668997014298+c.upper)) = pointBounds33605 := by
 decide +kernel
def cuts33606 : List PrefixCut := [⟨17,99916694,99916756⟩,
⟨64,378274682,378274923⟩]
theorem checked33606 : checkPrefixCuts (2^48) 4408737793 10 Manual.Count131072.C033606.packed 64 cuts33606 = true := by
 decide +kernel
def pointBounds33606 : List (Nat × Nat × Nat) := [(4408772608,106669086907886,106669471067266)]
theorem point_links_checked33606 : (cuts33606.take 1).map (fun c => (4408737793-1+2*2^10*c.k,106668986991192+c.lower,106669371150510+c.upper)) = pointBounds33606 := by
 decide +kernel
def cuts33607 : List PrefixCut := [⟨21,120279397,120279471⟩,
⟨64,373602983,373603218⟩]
theorem checked33607 : checkPrefixCuts (2^48) 4408868865 10 Manual.Count131072.C033607.packed 64 cuts33607 = true := by
 decide +kernel
def pointBounds33607 : List (Nat × Nat × Nat) := [(4408911872,106669485545271,106669869704904)]
theorem point_links_checked33607 : (cuts33607.take 1).map (fun c => (4408868865-1+2*2^10*c.k,106669365265874+c.lower,106669749425433+c.upper)) = pointBounds33607 := by
 decide +kernel
def cuts33608 : List PrefixCut := [⟨25,148046382,148046471⟩,
⟨64,379784354,379784587⟩]
theorem checked33608 : checkPrefixCuts (2^48) 4408999937 10 Manual.Count131072.C033608.packed 64 cuts33608 = true := by
 decide +kernel
def pointBounds33608 : List (Nat × Nat × Nat) := [(4409051136,106669886915239,106670271075122)]
theorem point_links_checked33608 : (cuts33608.take 1).map (fun c => (4408999937-1+2*2^10*c.k,106669738868857+c.lower,106670123028651+c.upper)) = pointBounds33608 := by
 decide +kernel
def cuts33609 : List PrefixCut := [⟨29,170002317,170002427⟩,
⟨64,371793307,371793545⟩]
theorem checked33609 : checkPrefixCuts (2^48) 4409131009 10 Manual.Count131072.C033609.packed 64 cuts33609 = true := by
 decide +kernel
def pointBounds33609 : List (Nat × Nat × Nat) := [(4409190400,106670288655528,106670672815665)]
theorem point_links_checked33609 : (cuts33609.take 1).map (fun c => (4409131009-1+2*2^10*c.k,106670118653211+c.lower,106670502813238+c.upper)) = pointBounds33609 := by
 decide +kernel
def cuts33610 : List PrefixCut := [⟨33,193297522,193297643⟩,
⟨64,377846661,377846899⟩]
theorem checked33610 : checkPrefixCuts (2^48) 4409262081 10 Manual.Count131072.C033610.packed 64 cuts33610 = true := by
 decide +kernel
def pointBounds33610 : List (Nat × Nat × Nat) := [(4409329664,106670683744040,106671067904426)]
theorem point_links_checked33610 : (cuts33610.take 1).map (fun c => (4409262081-1+2*2^10*c.k,106670490446518+c.lower,106670874606783+c.upper)) = pointBounds33610 := by
 decide +kernel
def cuts33611 : List PrefixCut := [⟨37,215378426,215378558⟩,
⟨64,378090763,378091000⟩]
theorem checked33611 : checkPrefixCuts (2^48) 4409393153 10 Manual.Count131072.C033611.packed 64 cuts33611 = true := by
 decide +kernel
def pointBounds33611 : List (Nat × Nat × Nat) := [(4409468928,106671083671605,106671467832240)]
theorem point_links_checked33611 : (cuts33611.take 1).map (fun c => (4409393153-1+2*2^10*c.k,106670868293179+c.lower,106671252453682+c.upper)) = pointBounds33611 := by
 decide +kernel
def cuts33612 : List PrefixCut := [⟨41,242436908,242437063⟩,
⟨64,379675353,379675595⟩]
theorem checked33612 : checkPrefixCuts (2^48) 4409524225 10 Manual.Count131072.C033612.packed 64 cuts33612 = true := by
 decide +kernel
def pointBounds33612 : List (Nat × Nat × Nat) := [(4409608192,106671488820850,106671872981745)]
theorem point_links_checked33612 : (cuts33612.take 1).map (fun c => (4409524225-1+2*2^10*c.k,106671246383942+c.lower,106671630544682+c.upper)) = pointBounds33612 := by
 decide +kernel
def cuts33613 : List PrefixCut := [⟨45,262089395,262089562⟩,
⟨64,374429983,374430220⟩]
theorem checked33613 : checkPrefixCuts (2^48) 4409655297 10 Manual.Count131072.C033613.packed 64 cuts33613 = true := by
 decide +kernel
def pointBounds33613 : List (Nat × Nat × Nat) := [(4409747456,106671888148690,106672272309839)]
theorem point_links_checked33613 : (cuts33613.take 1).map (fun c => (4409655297-1+2*2^10*c.k,106671626059295+c.lower,106672010220277+c.upper)) = pointBounds33613 := by
 decide +kernel
def cuts33614 : List PrefixCut := [⟨49,291059629,291059817⟩,
⟨64,380610201,380610444⟩]
theorem checked33614 : checkPrefixCuts (2^48) 4409786369 10 Manual.Count131072.C033614.packed 64 cuts33614 = true := by
 decide +kernel
def pointBounds33614 : List (Nat × Nat × Nat) := [(4409886720,106672291548907,106672675710314)]
theorem point_links_checked33614 : (cuts33614.take 1).map (fun c => (4409786369-1+2*2^10*c.k,106672000489278+c.lower,106672384650497+c.upper)) = pointBounds33614 := by
 decide +kernel
def cuts33615 : List PrefixCut := [⟨53,308730786,308730981⟩,
⟨64,374599183,374599419⟩]
theorem checked33615 : checkPrefixCuts (2^48) 4409917441 10 Manual.Count131072.C033615.packed 64 cuts33615 = true := by
 decide +kernel
def pointBounds33615 : List (Nat × Nat × Nat) := [(4410025984,106672689830265,106673073991922)]
theorem point_links_checked33615 : (cuts33615.take 1).map (fun c => (4409917441-1+2*2^10*c.k,106672381099479+c.lower,106672765260941+c.upper)) = pointBounds33615 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S4.B000112
