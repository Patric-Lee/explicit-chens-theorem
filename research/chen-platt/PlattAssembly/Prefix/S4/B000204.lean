import PlattAssemblyKernel
import PlattCertificates.Count131072.C036528
import PlattCertificates.Count131072.C036529
import PlattCertificates.Count131072.C036530
import PlattCertificates.Count131072.C036531
import PlattCertificates.Count131072.C036532
import PlattCertificates.Count131072.C036533
import PlattCertificates.Count131072.C036534
import PlattCertificates.Count131072.C036535
import PlattCertificates.Count131072.C036536
import PlattCertificates.Count131072.C036537
import PlattCertificates.Count131072.C036538
import PlattCertificates.Count131072.C036539
import PlattCertificates.Count131072.C036540
import PlattCertificates.Count131072.C036541
import PlattCertificates.Count131072.C036542
import PlattCertificates.Count131072.C036543
import PlattCertificates.Count131072.C036544
import PlattCertificates.Count131072.C036545
import PlattCertificates.Count131072.C036546
import PlattCertificates.Count131072.C036547
import PlattCertificates.Count131072.C036548
import PlattCertificates.Count131072.C036549
import PlattCertificates.Count131072.C036550
import PlattCertificates.Count131072.C036551
import PlattCertificates.Count131072.C036552
import PlattCertificates.Count131072.C036553
import PlattCertificates.Count131072.C036554
import PlattCertificates.Count131072.C036555
import PlattCertificates.Count131072.C036556
import PlattCertificates.Count131072.C036557
import PlattCertificates.Count131072.C036558
import PlattCertificates.Count131072.C036559
namespace ChenEffective.PlattWindow.Assembly.Prefix.S4.B000204
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts36528 : List PrefixCut := [⟨1,5521729,5521732⟩,
⟨64,345103429,345103640⟩]
theorem checked36528 : checkPrefixCuts (2^48) 4791730177 10 Manual.Count131072.C036528.packed 64 cuts36528 = true := by
 decide +kernel
def pointBounds36528 : List (Nat × Nat × Nat) := [(4791732224,107722883990038,107723268806124)]
theorem point_links_checked36528 : (cuts36528.take 1).map (fun c => (4791730177-1+2*2^10*c.k,107722878468309+c.lower,107723263284392+c.upper)) = pointBounds36528 := by
 decide +kernel
def cuts36529 : List PrefixCut := [⟨11,61265886,61265922⟩,
⟨64,346621221,346621428⟩]
theorem checked36529 : checkPrefixCuts (2^48) 4791861249 10 Manual.Count131072.C036529.packed 64 cuts36529 = true := by
 decide +kernel
def pointBounds36529 : List (Nat × Nat × Nat) := [(4791883776,107723284837624,107723669653954)]
theorem point_links_checked36529 : (cuts36529.take 1).map (fun c => (4791861249-1+2*2^10*c.k,107723223571738+c.lower,107723608388032+c.upper)) = pointBounds36529 := by
 decide +kernel
def cuts36530 : List PrefixCut := [⟨21,113658676,113658746⟩,
⟨64,347786451,347786670⟩]
theorem checked36530 : checkPrefixCuts (2^48) 4791992321 10 Manual.Count131072.C036530.packed 64 cuts36530 = true := by
 decide +kernel
def pointBounds36530 : List (Nat × Nat × Nat) := [(4792035328,107723683851635,107724068668206)]
theorem point_links_checked36530 : (cuts36530.take 1).map (fun c => (4791992321-1+2*2^10*c.k,107723570192959+c.lower,107723955009460+c.upper)) = pointBounds36530 := by
 decide +kernel
def cuts36531 : List PrefixCut := [⟨31,165578468,165578569⟩,
⟨64,344957585,344957793⟩]
theorem checked36531 : checkPrefixCuts (2^48) 4792123393 10 Manual.Count131072.C036531.packed 64 cuts36531 = true := by
 decide +kernel
def pointBounds36531 : List (Nat × Nat × Nat) := [(4792186880,107724083557878,107724468374699)]
theorem point_links_checked36531 : (cuts36531.take 1).map (fun c => (4792123393-1+2*2^10*c.k,107723917979410+c.lower,107724302796130+c.upper)) = pointBounds36531 := by
 decide +kernel
def cuts36532 : List PrefixCut := [⟨41,220079559,220079690⟩,
⟨64,344302098,344302306⟩]
theorem checked36532 : checkPrefixCuts (2^48) 4792254465 10 Manual.Count131072.C036532.packed 64 cuts36532 = true := by
 decide +kernel
def pointBounds36532 : List (Nat × Nat × Nat) := [(4792338432,107724483016554,107724867833613)]
theorem point_links_checked36532 : (cuts36532.take 1).map (fun c => (4792254465-1+2*2^10*c.k,107724262936995+c.lower,107724647753923+c.upper)) = pointBounds36532 := by
 decide +kernel
def cuts36533 : List PrefixCut := [⟨51,276045742,276045911⟩,
⟨64,344527638,344527849⟩]
theorem checked36533 : checkPrefixCuts (2^48) 4792385537 10 Manual.Count131072.C036533.packed 64 cuts36533 = true := by
 decide +kernel
def pointBounds36533 : List (Nat × Nat × Nat) := [(4792489984,107724883284835,107725268102140)]
theorem point_links_checked36533 : (cuts36533.take 1).map (fun c => (4792385537-1+2*2^10*c.k,107724607239093+c.lower,107724992056229+c.upper)) = pointBounds36533 := by
 decide +kernel
def cuts36534 : List PrefixCut := [⟨61,332360973,332361171⟩,
⟨64,348159503,348159712⟩]
theorem checked36534 : checkPrefixCuts (2^48) 4792516609 10 Manual.Count131072.C036534.packed 64 cuts36534 = true := by
 decide +kernel
def pointBounds36534 : List (Nat × Nat × Nat) := [(4792641536,107725284127704,107725668945249)]
theorem point_links_checked36534 : (cuts36534.take 1).map (fun c => (4792516609-1+2*2^10*c.k,107724951766731+c.lower,107725336584078+c.upper)) = pointBounds36534 := by
 decide +kernel
def cuts36535 : List PrefixCut := [⟨64,348678559,348678770⟩]
theorem checked36535 : checkPrefixCuts (2^48) 4792647681 10 Manual.Count131072.C036535.packed 64 cuts36535 = true := by
 decide +kernel
def cuts36536 : List PrefixCut := [⟨7,36940459,36940481⟩,
⟨64,344146955,344147166⟩]
theorem checked36536 : checkPrefixCuts (2^48) 4792778753 10 Manual.Count131072.C036536.packed 64 cuts36536 = true := by
 decide +kernel
def pointBounds36536 : List (Nat × Nat × Nat) := [(4792793088,107725685545252,107726070363041)]
theorem point_links_checked36536 : (cuts36536.take 1).map (fun c => (4792778753-1+2*2^10*c.k,107725648604793+c.lower,107726033422560+c.upper)) = pointBounds36536 := by
 decide +kernel
def cuts36537 : List PrefixCut := [⟨17,94022142,94022200⟩,
⟨64,349599122,349599331⟩]
theorem checked36537 : checkPrefixCuts (2^48) 4792909825 10 Manual.Count131072.C036537.packed 64 cuts36537 = true := by
 decide +kernel
def pointBounds36537 : List (Nat × Nat × Nat) := [(4792944640,107726086773890,107726471591926)]
theorem point_links_checked36537 : (cuts36537.take 1).map (fun c => (4792909825-1+2*2^10*c.k,107725992751748+c.lower,107726377569726+c.upper)) = pointBounds36537 := by
 decide +kernel
def cuts36538 : List PrefixCut := [⟨27,146226262,146226351⟩,
⟨64,347181876,347182087⟩]
theorem checked36538 : checkPrefixCuts (2^48) 4793040897 10 Manual.Count131072.C036538.packed 64 cuts36538 = true := by
 decide +kernel
def pointBounds36538 : List (Nat × Nat × Nat) := [(4793096192,107726488577132,107726873395408)]
theorem point_links_checked36538 : (cuts36538.take 1).map (fun c => (4793040897-1+2*2^10*c.k,107726342350870+c.lower,107726727169057+c.upper)) = pointBounds36538 := by
 decide +kernel
def cuts36539 : List PrefixCut := [⟨37,195726013,195726131⟩,
⟨64,343179141,343179351⟩]
theorem checked36539 : checkPrefixCuts (2^48) 4793171969 10 Manual.Count131072.C036539.packed 64 cuts36539 = true := by
 decide +kernel
def pointBounds36539 : List (Nat × Nat × Nat) := [(4793247744,107726885258759,107727270077275)]
theorem point_links_checked36539 : (cuts36539.take 1).map (fun c => (4793171969-1+2*2^10*c.k,107726689532746+c.lower,107727074351144+c.upper)) = pointBounds36539 := by
 decide +kernel
def cuts36540 : List PrefixCut := [⟨47,249803143,249803295⟩,
⟨64,341643008,341643217⟩]
theorem checked36540 : checkPrefixCuts (2^48) 4793303041 10 Manual.Count131072.C036540.packed 64 cuts36540 = true := by
 decide +kernel
def pointBounds36540 : List (Nat × Nat × Nat) := [(4793399296,107727282515030,107727667333790)]
theorem point_links_checked36540 : (cuts36540.take 1).map (fun c => (4793303041-1+2*2^10*c.k,107727032711887+c.lower,107727417530495+c.upper)) = pointBounds36540 := by
 decide +kernel
def cuts36541 : List PrefixCut := [⟨57,310629933,310630118⟩,
⟨64,348621390,348621598⟩]
theorem checked36541 : checkPrefixCuts (2^48) 4793434113 10 Manual.Count131072.C036541.packed 64 cuts36541 = true := by
 decide +kernel
def pointBounds36541 : List (Nat × Nat × Nat) := [(4793550848,107727684984828,107728069803830)]
theorem point_links_checked36541 : (cuts36541.take 1).map (fun c => (4793434113-1+2*2^10*c.k,107727374354895+c.lower,107727759173712+c.upper)) = pointBounds36541 := by
 decide +kernel
def cuts36542 : List PrefixCut := [⟨64,345264935,345265142⟩]
theorem checked36542 : checkPrefixCuts (2^48) 4793565185 10 Manual.Count131072.C036542.packed 64 cuts36542 = true := by
 decide +kernel
def cuts36543 : List PrefixCut := [⟨3,16910691,16910701⟩,
⟨64,346840828,346841043⟩]
theorem checked36543 : checkPrefixCuts (2^48) 4793696257 10 Manual.Count131072.C036543.packed 64 cuts36543 = true := by
 decide +kernel
def pointBounds36543 : List (Nat × Nat × Nat) := [(4793702400,107728085151911,107728469971153)]
theorem point_links_checked36543 : (cuts36543.take 1).map (fun c => (4793696257-1+2*2^10*c.k,107728068241220+c.lower,107728453060452+c.upper)) = pointBounds36543 := by
 decide +kernel
def cuts36544 : List PrefixCut := [⟨13,69637111,69637153⟩,
⟨64,344717564,344717772⟩]
theorem checked36544 : checkPrefixCuts (2^48) 4793827329 10 Manual.Count131072.C036544.packed 64 cuts36544 = true := by
 decide +kernel
def pointBounds36544 : List (Nat × Nat × Nat) := [(4793853952,107728484719159,107728869538648)]
theorem point_links_checked36544 : (cuts36544.take 1).map (fun c => (4793827329-1+2*2^10*c.k,107728415082048+c.lower,107728799901495+c.upper)) = pointBounds36544 := by
 decide +kernel
def cuts36545 : List PrefixCut := [⟨23,121362286,121362358⟩,
⟨64,343122834,343123045⟩]
theorem checked36545 : checkPrefixCuts (2^48) 4793958401 10 Manual.Count131072.C036545.packed 64 cuts36545 = true := by
 decide +kernel
def pointBounds36545 : List (Nat × Nat × Nat) := [(4794005504,107728881161898,107729265981625)]
theorem point_links_checked36545 : (cuts36545.take 1).map (fun c => (4793958401-1+2*2^10*c.k,107728759799612+c.lower,107729144619267+c.upper)) = pointBounds36545 := by
 decide +kernel
def cuts36546 : List PrefixCut := [⟨33,177663961,177664072⟩,
⟨64,343994169,343994377⟩]
theorem checked36546 : checkPrefixCuts (2^48) 4794089473 10 Manual.Count131072.C036546.packed 64 cuts36546 = true := by
 decide +kernel
def pointBounds36546 : List (Nat × Nat × Nat) := [(4794157056,107729280586407,107729665406384)]
theorem point_links_checked36546 : (cuts36546.take 1).map (fun c => (4794089473-1+2*2^10*c.k,107729102922446+c.lower,107729487742312+c.upper)) = pointBounds36546 := by
 decide +kernel
def cuts36547 : List PrefixCut := [⟨43,230381013,230381153⟩,
⟨64,347272535,347272745⟩]
theorem checked36547 : checkPrefixCuts (2^48) 4794220545 10 Manual.Count131072.C036547.packed 64 cuts36547 = true := by
 decide +kernel
def pointBounds36547 : List (Nat × Nat × Nat) := [(4794308608,107729677297628,107730062117842)]
theorem point_links_checked36547 : (cuts36547.take 1).map (fun c => (4794220545-1+2*2^10*c.k,107729446916615+c.lower,107729831736689+c.upper)) = pointBounds36547 := by
 decide +kernel
def cuts36548 : List PrefixCut := [⟨53,281274924,281275099⟩,
⟨64,342801138,342801351⟩]
theorem checked36548 : checkPrefixCuts (2^48) 4794351617 10 Manual.Count131072.C036548.packed 64 cuts36548 = true := by
 decide +kernel
def pointBounds36548 : List (Nat × Nat × Nat) := [(4794460160,107730075464074,107730460284533)]
theorem point_links_checked36548 : (cuts36548.take 1).map (fun c => (4794351617-1+2*2^10*c.k,107729794189150+c.lower,107730179009434+c.upper)) = pointBounds36548 := by
 decide +kernel
def cuts36549 : List PrefixCut := [⟨63,338682363,338682564⟩,
⟨64,345140077,345140282⟩]
theorem checked36549 : checkPrefixCuts (2^48) 4794482689 10 Manual.Count131072.C036549.packed 64 cuts36549 = true := by
 decide +kernel
def pointBounds36549 : List (Nat × Nat × Nat) := [(4794611712,107730475672651,107730860493349)]
theorem point_links_checked36549 : (cuts36549.take 1).map (fun c => (4794482689-1+2*2^10*c.k,107730136990288+c.lower,107730521810785+c.upper)) = pointBounds36549 := by
 decide +kernel
def cuts36550 : List PrefixCut := [⟨64,345952538,345952757⟩]
theorem checked36550 : checkPrefixCuts (2^48) 4794613761 10 Manual.Count131072.C036550.packed 64 cuts36550 = true := by
 decide +kernel
def cuts36551 : List PrefixCut := [⟨9,47374743,47374772⟩,
⟨64,342890471,342890679⟩]
theorem checked36551 : checkPrefixCuts (2^48) 4794744833 10 Manual.Count131072.C036551.packed 64 cuts36551 = true := by
 decide +kernel
def pointBounds36551 : List (Nat × Nat × Nat) := [(4794763264,107730875457646,107731260278596)]
theorem point_links_checked36551 : (cuts36551.take 1).map (fun c => (4794744833-1+2*2^10*c.k,107730828082903+c.lower,107731212903824+c.upper)) = pointBounds36551 := by
 decide +kernel
def cuts36552 : List PrefixCut := [⟨19,105958964,105959028⟩,
⟨64,350864635,350864851⟩]
theorem checked36552 : checkPrefixCuts (2^48) 4794875905 10 Manual.Count131072.C036552.packed 64 cuts36552 = true := by
 decide +kernel
def pointBounds36552 : List (Nat × Nat × Nat) := [(4794914816,107731276932338,107731661753531)]
theorem point_links_checked36552 : (cuts36552.take 1).map (fun c => (4794875905-1+2*2^10*c.k,107731170973374+c.lower,107731555794503+c.upper)) = pointBounds36552 := by
 decide +kernel
def cuts36553 : List PrefixCut := [⟨29,155264938,155265033⟩,
⟨64,343223926,343224134⟩]
theorem checked36553 : checkPrefixCuts (2^48) 4795006977 10 Manual.Count131072.C036553.packed 64 cuts36553 = true := by
 decide +kernel
def pointBounds36553 : List (Nat × Nat × Nat) := [(4795066368,107731677102947,107732061924387)]
theorem point_links_checked36553 : (cuts36553.take 1).map (fun c => (4795006977-1+2*2^10*c.k,107731521838009+c.lower,107731906659354+c.upper)) = pointBounds36553 := by
 decide +kernel
def cuts36554 : List PrefixCut := [⟨39,212257658,212257788⟩,
⟨64,349436675,349436887⟩]
theorem checked36554 : checkPrefixCuts (2^48) 4795138049 10 Manual.Count131072.C036554.packed 64 cuts36554 = true := by
 decide +kernel
def pointBounds36554 : List (Nat × Nat × Nat) := [(4795217920,107732077319593,107732462141276)]
theorem point_links_checked36554 : (cuts36554.take 1).map (fun c => (4795138049-1+2*2^10*c.k,107731865061935+c.lower,107732249883488+c.upper)) = pointBounds36554 := by
 decide +kernel
def cuts36555 : List PrefixCut := [⟨49,263670701,263670862⟩,
⟨64,345905248,345905456⟩]
theorem checked36555 : checkPrefixCuts (2^48) 4795269121 10 Manual.Count131072.C036555.packed 64 cuts36555 = true := by
 decide +kernel
def pointBounds36555 : List (Nat × Nat × Nat) := [(4795369472,107732478169311,107732862991237)]
theorem point_links_checked36555 : (cuts36555.take 1).map (fun c => (4795269121-1+2*2^10*c.k,107732214498610+c.lower,107732599320375+c.upper)) = pointBounds36555 := by
 decide +kernel
def cuts36556 : List PrefixCut := [⟨59,321067771,321067965⟩,
⟨64,345954582,345954793⟩]
theorem checked36556 : checkPrefixCuts (2^48) 4795400193 10 Manual.Count131072.C036556.packed 64 cuts36556 = true := by
 decide +kernel
def pointBounds36556 : List (Nat × Nat × Nat) := [(4795521024,107732881471629,107733266293796)]
theorem point_links_checked36556 : (cuts36556.take 1).map (fun c => (4795400193-1+2*2^10*c.k,107732560403858+c.lower,107732945225831+c.upper)) = pointBounds36556 := by
 decide +kernel
def cuts36557 : List PrefixCut := [⟨64,343127745,343127951⟩]
theorem checked36557 : checkPrefixCuts (2^48) 4795531265 10 Manual.Count131072.C036557.packed 64 cuts36557 = true := by
 decide +kernel
def cuts36558 : List PrefixCut := [⟨5,26588192,26588209⟩,
⟨64,342824892,342825103⟩]
theorem checked36558 : checkPrefixCuts (2^48) 4795662337 10 Manual.Count131072.C036558.packed 64 cuts36558 = true := by
 decide +kernel
def pointBounds36558 : List (Nat × Nat × Nat) := [(4795672576,107733276074377,107733660896784)]
theorem point_links_checked36558 : (cuts36558.take 1).map (fun c => (4795662337-1+2*2^10*c.k,107733249486185+c.lower,107733634308575+c.upper)) = pointBounds36558 := by
 decide +kernel
def cuts36559 : List PrefixCut := [⟨15,80349145,80349193⟩,
⟨64,344752335,344752550⟩]
theorem checked36559 : checkPrefixCuts (2^48) 4795793409 10 Manual.Count131072.C036559.packed 64 cuts36559 = true := by
 decide +kernel
def pointBounds36559 : List (Nat × Nat × Nat) := [(4795824128,107733672660222,107734057482871)]
theorem point_links_checked36559 : (cuts36559.take 1).map (fun c => (4795793409-1+2*2^10*c.k,107733592311077+c.lower,107733977133678+c.upper)) = pointBounds36559 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S4.B000204
