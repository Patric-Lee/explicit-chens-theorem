import PlattAssemblyKernel
import PlattCertificates.Count131072.C041536
import PlattCertificates.Count131072.C041537
import PlattCertificates.Count131072.C041538
import PlattCertificates.Count131072.C041539
import PlattCertificates.Count131072.C041540
import PlattCertificates.Count131072.C041541
import PlattCertificates.Count131072.C041542
import PlattCertificates.Count131072.C041543
import PlattCertificates.Count131072.C041544
import PlattCertificates.Count131072.C041545
import PlattCertificates.Count131072.C041546
import PlattCertificates.Count131072.C041547
import PlattCertificates.Count131072.C041548
import PlattCertificates.Count131072.C041549
import PlattCertificates.Count131072.C041550
import PlattCertificates.Count131072.C041551
import PlattCertificates.Count131072.C041552
import PlattCertificates.Count131072.C041553
import PlattCertificates.Count131072.C041554
import PlattCertificates.Count131072.C041555
import PlattCertificates.Count131072.C041556
import PlattCertificates.Count131072.C041557
import PlattCertificates.Count131072.C041558
import PlattCertificates.Count131072.C041559
import PlattCertificates.Count131072.C041560
import PlattCertificates.Count131072.C041561
import PlattCertificates.Count131072.C041562
import PlattCertificates.Count131072.C041563
import PlattCertificates.Count131072.C041564
import PlattCertificates.Count131072.C041565
import PlattCertificates.Count131072.C041566
import PlattCertificates.Count131072.C041567
namespace ChenEffective.PlattWindow.Assembly.Prefix.S5.B000048
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts41536 : List PrefixCut := [⟨64,301871544,301871720⟩]
theorem checked41536 : checkPrefixCuts (2^48) 5448138753 10 Manual.Count131072.C041536.packed 64 cuts41536 = true := by
 decide +kernel
def cuts41537 : List PrefixCut := [⟨9,42208741,42208768⟩,
⟨64,305325641,305325820⟩]
theorem checked41537 : checkPrefixCuts (2^48) 5448269825 10 Manual.Count131072.C041537.packed 64 cuts41537 = true := by
 decide +kernel
def pointBounds41537 : List (Nat × Nat × Nat) := [(5448288256,109339689352686,109340075138183)]
theorem point_links_checked41537 : (cuts41537.take 1).map (fun c => (5448269825-1+2*2^10*c.k,109339647143945+c.lower,109340032929415+c.upper)) = pointBounds41537 := by
 decide +kernel
def cuts41538 : List PrefixCut := [⟨29,138039911,138039992⟩,
⟨64,298447388,298447563⟩]
theorem checked41538 : checkPrefixCuts (2^48) 5448400897 10 Manual.Count131072.C041538.packed 64 cuts41538 = true := by
 decide +kernel
def pointBounds41538 : List (Nat × Nat × Nat) := [(5448460288,109340090509497,109340476295227)]
theorem point_links_checked41538 : (cuts41538.take 1).map (fun c => (5448400897-1+2*2^10*c.k,109339952469586+c.lower,109340338255235+c.upper)) = pointBounds41538 := by
 decide +kernel
def cuts41539 : List PrefixCut := [⟨49,231541074,231541209⟩,
⟨64,302418029,302418206⟩]
theorem checked41539 : checkPrefixCuts (2^48) 5448531969 10 Manual.Count131072.C041539.packed 64 cuts41539 = true := by
 decide +kernel
def pointBounds41539 : List (Nat × Nat × Nat) := [(5448632320,109340482458048,109340868244007)]
theorem point_links_checked41539 : (cuts41539.take 1).map (fun c => (5448531969-1+2*2^10*c.k,109340250916974+c.lower,109340636702798+c.upper)) = pointBounds41539 := by
 decide +kernel
def cuts41540 : List PrefixCut := [⟨64,302978964,302979145⟩]
theorem checked41540 : checkPrefixCuts (2^48) 5448663041 10 Manual.Count131072.C041540.packed 64 cuts41540 = true := by
 decide +kernel
def cuts41541 : List PrefixCut := [⟨5,23452800,23452814⟩,
⟨64,301060379,301060554⟩]
theorem checked41541 : checkPrefixCuts (2^48) 5448794113 10 Manual.Count131072.C041541.packed 64 cuts41541 = true := by
 decide +kernel
def pointBounds41541 : List (Nat × Nat × Nat) := [(5448804352,109340879766767,109341265552963)]
theorem point_links_checked41541 : (cuts41541.take 1).map (fun c => (5448794113-1+2*2^10*c.k,109340856313967+c.lower,109341242100149+c.upper)) = pointBounds41541 := by
 decide +kernel
def cuts41542 : List PrefixCut := [⟨25,114884533,114884602⟩,
⟨64,298160328,298160509⟩]
theorem checked41542 : checkPrefixCuts (2^48) 5448925185 10 Manual.Count131072.C041542.packed 64 cuts41542 = true := by
 decide +kernel
def pointBounds41542 : List (Nat × Nat × Nat) := [(5448976384,109341272258879,109341658045305)]
theorem point_links_checked41542 : (cuts41542.take 1).map (fun c => (5448925185-1+2*2^10*c.k,109341157374346+c.lower,109341543160703+c.upper)) = pointBounds41542 := by
 decide +kernel
def cuts41543 : List PrefixCut := [⟨45,214317761,214317890⟩,
⟨64,304351826,304352011⟩]
theorem checked41543 : checkPrefixCuts (2^48) 5449056257 10 Manual.Count131072.C041543.packed 64 cuts41543 = true := by
 decide +kernel
def pointBounds41543 : List (Nat × Nat × Nat) := [(5449148416,109341669852435,109342055639102)]
theorem point_links_checked41543 : (cuts41543.take 1).map (fun c => (5449056257-1+2*2^10*c.k,109341455534674+c.lower,109341841321212+c.upper)) = pointBounds41543 := by
 decide +kernel
def cuts41544 : List PrefixCut := [⟨64,303621354,303621533⟩]
theorem checked41544 : checkPrefixCuts (2^48) 5449187329 10 Manual.Count131072.C041544.packed 64 cuts41544 = true := by
 decide +kernel
def cuts41545 : List PrefixCut := [⟨1,4597137,4597139⟩,
⟨64,307023098,307023273⟩]
theorem checked41545 : checkPrefixCuts (2^48) 5449318401 10 Manual.Count131072.C041545.packed 64 cuts41545 = true := by
 decide +kernel
def pointBounds41545 : List (Nat × Nat × Nat) := [(5449320448,109342068104991,109342453891895)]
theorem point_links_checked41545 : (cuts41545.take 1).map (fun c => (5449318401-1+2*2^10*c.k,109342063507854+c.lower,109342449294756+c.upper)) = pointBounds41545 := by
 decide +kernel
def cuts41546 : List PrefixCut := [⟨21,101702354,101702416⟩,
⟨64,302831968,302832148⟩]
theorem checked41546 : checkPrefixCuts (2^48) 5449449473 10 Manual.Count131072.C041546.packed 64 cuts41546 = true := by
 decide +kernel
def pointBounds41546 : List (Nat × Nat × Nat) := [(5449492480,109342472233306,109342858020445)]
theorem point_links_checked41546 : (cuts41546.take 1).map (fun c => (5449449473-1+2*2^10*c.k,109342370530952+c.lower,109342756318029+c.upper)) = pointBounds41546 := by
 decide +kernel
def cuts41547 : List PrefixCut := [⟨41,194463584,194463695⟩,
⟨64,300448813,300448992⟩]
theorem checked41547 : checkPrefixCuts (2^48) 5449580545 10 Manual.Count131072.C041547.packed 64 cuts41547 = true := by
 decide +kernel
def pointBounds41547 : List (Nat × Nat × Nat) := [(5449664512,109342867826504,109343253613872)]
theorem point_links_checked41547 : (cuts41547.take 1).map (fun c => (5449580545-1+2*2^10*c.k,109342673362920+c.lower,109343059150177+c.upper)) = pointBounds41547 := by
 decide +kernel
def cuts41548 : List PrefixCut := [⟨61,283190973,283191142⟩,
⟨64,298272274,298272451⟩]
theorem checked41548 : checkPrefixCuts (2^48) 5449711617 10 Manual.Count131072.C041548.packed 64 cuts41548 = true := by
 decide +kernel
def pointBounds41548 : List (Nat × Nat × Nat) := [(5449836544,109343257002706,109343642790311)]
theorem point_links_checked41548 : (cuts41548.take 1).map (fun c => (5449711617-1+2*2^10*c.k,109342973811733+c.lower,109343359599169+c.upper)) = pointBounds41548 := by
 decide +kernel
def cuts41549 : List PrefixCut := [⟨64,303998013,303998190⟩]
theorem checked41549 : checkPrefixCuts (2^48) 5449842689 10 Manual.Count131072.C041549.packed 64 cuts41549 = true := by
 decide +kernel
def cuts41550 : List PrefixCut := [⟨17,79329559,79329609⟩,
⟨64,304610454,304610635⟩]
theorem checked41550 : checkPrefixCuts (2^48) 5449973761 10 Manual.Count131072.C041550.packed 64 cuts41550 = true := by
 decide +kernel
def pointBounds41550 : List (Nat × Nat × Nat) := [(5450008576,109343655411579,109344041199419)]
theorem point_links_checked41550 : (cuts41550.take 1).map (fun c => (5449973761-1+2*2^10*c.k,109343576082020+c.lower,109343961869810+c.upper)) = pointBounds41550 := by
 decide +kernel
def cuts41551 : List PrefixCut := [⟨37,176265808,176265908⟩,
⟨64,304499829,304500008⟩]
theorem checked41551 : checkPrefixCuts (2^48) 5450104833 10 Manual.Count131072.C041551.packed 64 cuts41551 = true := by
 decide +kernel
def pointBounds41551 : List (Nat × Nat × Nat) := [(5450180608,109344056958282,109344442746353)]
theorem point_links_checked41551 : (cuts41551.take 1).map (fun c => (5450104833-1+2*2^10*c.k,109343880692474+c.lower,109344266480445+c.upper)) = pointBounds41551 := by
 decide +kernel
def cuts41552 : List PrefixCut := [⟨57,270614461,270614617⟩,
⟨64,303614569,303614744⟩]
theorem checked41552 : checkPrefixCuts (2^48) 5450235905 10 Manual.Count131072.C041552.packed 64 cuts41552 = true := by
 decide +kernel
def pointBounds41552 : List (Nat × Nat × Nat) := [(5450352640,109344455806764,109344841595070)]
theorem point_links_checked41552 : (cuts41552.take 1).map (fun c => (5450235905-1+2*2^10*c.k,109344185192303+c.lower,109344570980453+c.upper)) = pointBounds41552 := by
 decide +kernel
def cuts41553 : List PrefixCut := [⟨64,301386630,301386811⟩]
theorem checked41553 : checkPrefixCuts (2^48) 5450366977 10 Manual.Count131072.C041553.packed 64 cuts41553 = true := by
 decide +kernel
def cuts41554 : List PrefixCut := [⟨13,59698063,59698098⟩,
⟨64,298848925,298849099⟩]
theorem checked41554 : checkPrefixCuts (2^48) 5450498049 10 Manual.Count131072.C041554.packed 64 cuts41554 = true := by
 decide +kernel
def pointBounds41554 : List (Nat × Nat × Nat) := [(5450524672,109344849891565,109345235680106)]
theorem point_links_checked41554 : (cuts41554.take 1).map (fun c => (5450498049-1+2*2^10*c.k,109344790193502+c.lower,109345175982008+c.upper)) = pointBounds41554 := by
 decide +kernel
def cuts41555 : List PrefixCut := [⟨33,155437876,155437969⟩,
⟨64,300442616,300442794⟩]
theorem checked41555 : checkPrefixCuts (2^48) 5450629121 10 Manual.Count131072.C041555.packed 64 cuts41555 = true := by
 decide +kernel
def pointBounds41555 : List (Nat × Nat × Nat) := [(5450696704,109345244480303,109345630269076)]
theorem point_links_checked41555 : (cuts41555.take 1).map (fun c => (5450629121-1+2*2^10*c.k,109345089042427+c.lower,109345474831107+c.upper)) = pointBounds41555 := by
 decide +kernel
def cuts41556 : List PrefixCut := [⟨53,249571531,249571677⟩,
⟨64,299144425,299144601⟩]
theorem checked41556 : checkPrefixCuts (2^48) 5450760193 10 Manual.Count131072.C041556.packed 64 cuts41556 = true := by
 decide +kernel
def pointBounds41556 : List (Nat × Nat × Nat) := [(5450868736,109345639056574,109346024845578)]
theorem point_links_checked41556 : (cuts41556.take 1).map (fun c => (5450760193-1+2*2^10*c.k,109345389485043+c.lower,109345775273901+c.upper)) = pointBounds41556 := by
 decide +kernel
def cuts41557 : List PrefixCut := [⟨64,303164944,303165126⟩]
theorem checked41557 : checkPrefixCuts (2^48) 5450891265 10 Manual.Count131072.C041557.packed 64 cuts41557 = true := by
 decide +kernel
def cuts41558 : List PrefixCut := [⟨9,41516145,41516170⟩,
⟨64,303364200,303364379⟩]
theorem checked41558 : checkPrefixCuts (2^48) 5451022337 10 Manual.Count131072.C041558.packed 64 cuts41558 = true := by
 decide +kernel
def pointBounds41558 : List (Nat × Nat × Nat) := [(5451040768,109346033310557,109346419099798)]
theorem point_links_checked41558 : (cuts41558.take 1).map (fun c => (5451022337-1+2*2^10*c.k,109345991794412+c.lower,109346377583628+c.upper)) = pointBounds41558 := by
 decide +kernel
def cuts41559 : List PrefixCut := [⟨29,138021861,138021943⟩,
⟨64,306455030,306455213⟩]
theorem checked41559 : checkPrefixCuts (2^48) 5451153409 10 Manual.Count131072.C041559.packed 64 cuts41559 = true := by
 decide +kernel
def pointBounds41559 : List (Nat × Nat × Nat) := [(5451212800,109346433180473,109346818969950)]
theorem point_links_checked41559 : (cuts41559.take 1).map (fun c => (5451153409-1+2*2^10*c.k,109346295158612+c.lower,109346680948007+c.upper)) = pointBounds41559 := by
 decide +kernel
def cuts41560 : List PrefixCut := [⟨49,232250315,232250446⟩,
⟨64,301335942,301336113⟩]
theorem checked41560 : checkPrefixCuts (2^48) 5451284481 10 Manual.Count131072.C041560.packed 64 cuts41560 = true := by
 decide +kernel
def pointBounds41560 : List (Nat × Nat × Nat) := [(5451384832,109346833863957,109347219653666)]
theorem point_links_checked41560 : (cuts41560.take 1).map (fun c => (5451284481-1+2*2^10*c.k,109346601613642+c.lower,109346987403220+c.upper)) = pointBounds41560 := by
 decide +kernel
def cuts41561 : List PrefixCut := [⟨64,304271774,304271954⟩]
theorem checked41561 : checkPrefixCuts (2^48) 5451415553 10 Manual.Count131072.C041561.packed 64 cuts41561 = true := by
 decide +kernel
def cuts41562 : List PrefixCut := [⟨5,22924639,22924653⟩,
⟨64,299772480,299772659⟩]
theorem checked41562 : checkPrefixCuts (2^48) 5451546625 10 Manual.Count131072.C041562.packed 64 cuts41562 = true := by
 decide +kernel
def pointBounds41562 : List (Nat × Nat × Nat) := [(5451556864,109347230145997,109347615935940)]
theorem point_links_checked41562 : (cuts41562.take 1).map (fun c => (5451546625-1+2*2^10*c.k,109347207221358+c.lower,109347593011287+c.upper)) = pointBounds41562 := by
 decide +kernel
def cuts41563 : List PrefixCut := [⟨25,116272191,116272258⟩,
⟨64,299403855,299404026⟩]
theorem checked41563 : checkPrefixCuts (2^48) 5451677697 10 Manual.Count131072.C041563.packed 64 cuts41563 = true := by
 decide +kernel
def pointBounds41563 : List (Nat × Nat × Nat) := [(5451728896,109347623266029,109348009056204)]
theorem point_links_checked41563 : (cuts41563.take 1).map (fun c => (5451677697-1+2*2^10*c.k,109347506993838+c.lower,109347892783946+c.upper)) = pointBounds41563 := by
 decide +kernel
def cuts41564 : List PrefixCut := [⟨45,212144393,212144519⟩,
⟨64,299861348,299861527⟩]
theorem checked41564 : checkPrefixCuts (2^48) 5451808769 10 Manual.Count131072.C041564.packed 64 cuts41564 = true := by
 decide +kernel
def pointBounds41564 : List (Nat × Nat × Nat) := [(5451900928,109348018542086,109348404332491)]
theorem point_links_checked41564 : (cuts41564.take 1).map (fun c => (5451808769-1+2*2^10*c.k,109347806397693+c.lower,109348192187972+c.upper)) = pointBounds41564 := by
 decide +kernel
def cuts41565 : List PrefixCut := [⟨64,302487122,302487297⟩]
theorem checked41565 : checkPrefixCuts (2^48) 5451939841 10 Manual.Count131072.C041565.packed 64 cuts41565 = true := by
 decide +kernel
def cuts41566 : List PrefixCut := [⟨1,4026917,4026920⟩,
⟨64,299537127,299537308⟩]
theorem checked41566 : checkPrefixCuts (2^48) 5452070913 10 Manual.Count131072.C041566.packed 64 cuts41566 = true := by
 decide +kernel
def pointBounds41566 : List (Nat × Nat × Nat) := [(5452072960,109348412773080,109348798563716)]
theorem point_links_checked41566 : (cuts41566.take 1).map (fun c => (5452070913-1+2*2^10*c.k,109348408746163+c.lower,109348794536796+c.upper)) = pointBounds41566 := by
 decide +kernel
def cuts41567 : List PrefixCut := [⟨21,99585991,99586050⟩,
⟨64,303556714,303556893⟩]
theorem checked41567 : checkPrefixCuts (2^48) 5452201985 10 Manual.Count131072.C041567.packed 64 cuts41567 = true := by
 decide +kernel
def pointBounds41567 : List (Nat × Nat × Nat) := [(5452244992,109348807869281,109349193660154)]
theorem point_links_checked41567 : (cuts41567.take 1).map (fun c => (5452201985-1+2*2^10*c.k,109348708283290+c.lower,109349094074104+c.upper)) = pointBounds41567 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S5.B000048
