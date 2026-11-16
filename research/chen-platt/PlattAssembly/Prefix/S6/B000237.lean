import PlattAssemblyKernel
import PlattCertificates.Count131072.C057584
import PlattCertificates.Count131072.C057585
import PlattCertificates.Count131072.C057586
import PlattCertificates.Count131072.C057587
import PlattCertificates.Count131072.C057588
import PlattCertificates.Count131072.C057589
import PlattCertificates.Count131072.C057590
import PlattCertificates.Count131072.C057591
import PlattCertificates.Count131072.C057592
import PlattCertificates.Count131072.C057593
import PlattCertificates.Count131072.C057594
import PlattCertificates.Count131072.C057595
import PlattCertificates.Count131072.C057596
import PlattCertificates.Count131072.C057597
import PlattCertificates.Count131072.C057598
import PlattCertificates.Count131072.C057599
import PlattCertificates.Count131072.C057600
import PlattCertificates.Count131072.C057601
import PlattCertificates.Count131072.C057602
import PlattCertificates.Count131072.C057603
import PlattCertificates.Count131072.C057604
import PlattCertificates.Count131072.C057605
import PlattCertificates.Count131072.C057606
import PlattCertificates.Count131072.C057607
import PlattCertificates.Count131072.C057608
import PlattCertificates.Count131072.C057609
import PlattCertificates.Count131072.C057610
import PlattCertificates.Count131072.C057611
import PlattCertificates.Count131072.C057612
import PlattCertificates.Count131072.C057613
import PlattCertificates.Count131072.C057614
import PlattCertificates.Count131072.C057615
namespace ChenEffective.PlattWindow.Assembly.Prefix.S6.B000237
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts57584 : List PrefixCut := [⟨64,214060614,214060735⟩]
theorem checked57584 : checkPrefixCuts (2^48) 7551582209 10 Manual.Count131072.C057584.packed 64 cuts57584 = true := by
 decide +kernel
def cuts57585 : List PrefixCut := [⟨4,13194629,13194637⟩,
⟨64,213199626,213199747⟩]
theorem checked57585 : checkPrefixCuts (2^48) 7551713281 10 Manual.Count131072.C057585.packed 64 cuts57585 = true := by
 decide +kernel
def pointBounds57585 : List (Nat × Nat × Nat) := [(7551721472,113409153255979,113409541373600)]
theorem point_links_checked57585 : (cuts57585.take 1).map (fun c => (7551713281-1+2*2^10*c.k,113409140061350+c.lower,113409528178963+c.upper)) = pointBounds57585 := by
 decide +kernel
def cuts57586 : List PrefixCut := [⟨56,188820211,188820321⟩,
⟨64,215804946,215805072⟩]
theorem checked57586 : checkPrefixCuts (2^48) 7551844353 10 Manual.Count131072.C057586.packed 64 cuts57586 = true := by
 decide +kernel
def pointBounds57586 : List (Nat × Nat × Nat) := [(7551959040,113409542081187,113409930199031)]
theorem point_links_checked57586 : (cuts57586.take 1).map (fun c => (7551844353-1+2*2^10*c.k,113409353260976+c.lower,113409741378710+c.upper)) = pointBounds57586 := by
 decide +kernel
def cuts57587 : List PrefixCut := [⟨64,211626835,211626957⟩]
theorem checked57587 : checkPrefixCuts (2^48) 7551975425 10 Manual.Count131072.C057587.packed 64 cuts57587 = true := by
 decide +kernel
def cuts57588 : List PrefixCut := [⟨44,148822393,148822478⟩,
⟨64,217884624,217884748⟩]
theorem checked57588 : checkPrefixCuts (2^48) 7552106497 10 Manual.Count131072.C057588.packed 64 cuts57588 = true := by
 decide +kernel
def pointBounds57588 : List (Nat × Nat × Nat) := [(7552196608,113409929515150,113410317633217)]
theorem point_links_checked57588 : (cuts57588.take 1).map (fun c => (7552106497-1+2*2^10*c.k,113409780692757+c.lower,113410168810739+c.upper)) = pointBounds57588 := by
 decide +kernel
def cuts57589 : List PrefixCut := [⟨64,214638376,214638495⟩]
theorem checked57589 : checkPrefixCuts (2^48) 7552237569 10 Manual.Count131072.C057589.packed 64 cuts57589 = true := by
 decide +kernel
def cuts57590 : List PrefixCut := [⟨32,106553760,106553820⟩,
⟨64,213851977,213852101⟩]
theorem checked57590 : checkPrefixCuts (2^48) 7552368641 10 Manual.Count131072.C057590.packed 64 cuts57590 = true := by
 decide +kernel
def pointBounds57590 : List (Nat × Nat × Nat) := [(7552434176,113410319769517,113410707887802)]
theorem point_links_checked57590 : (cuts57590.take 1).map (fun c => (7552368641-1+2*2^10*c.k,113410213215757+c.lower,113410601333982+c.upper)) = pointBounds57590 := by
 decide +kernel
def cuts57591 : List PrefixCut := [⟨64,213922814,213922934⟩]
theorem checked57591 : checkPrefixCuts (2^48) 7552499713 10 Manual.Count131072.C057591.packed 64 cuts57591 = true := by
 decide +kernel
def cuts57592 : List PrefixCut := [⟨20,67306646,67306686⟩,
⟨64,216676921,216677048⟩]
theorem checked57592 : checkPrefixCuts (2^48) 7552630785 10 Manual.Count131072.C057592.packed 64 cuts57592 = true := by
 decide +kernel
def pointBounds57592 : List (Nat × Nat × Nat) := [(7552671744,113410708297194,113411096415703)]
theorem point_links_checked57592 : (cuts57592.take 1).map (fun c => (7552630785-1+2*2^10*c.k,113410640990548+c.lower,113411029109017+c.upper)) = pointBounds57592 := by
 decide +kernel
def cuts57593 : List PrefixCut := [⟨64,217418539,217418664⟩]
theorem checked57593 : checkPrefixCuts (2^48) 7552761857 10 Manual.Count131072.C057593.packed 64 cuts57593 = true := by
 decide +kernel
def cuts57594 : List PrefixCut := [⟨8,28211212,28211228⟩,
⟨64,216520355,216520479⟩]
theorem checked57594 : checkPrefixCuts (2^48) 7552892929 10 Manual.Count131072.C057594.packed 64 cuts57594 = true := by
 decide +kernel
def pointBounds57594 : List (Nat × Nat × Nat) := [(7552909312,113411103297220,113411491415957)]
theorem point_links_checked57594 : (cuts57594.take 1).map (fun c => (7552892929-1+2*2^10*c.k,113411075086008+c.lower,113411463204729+c.upper)) = pointBounds57594 := by
 decide +kernel
def cuts57595 : List PrefixCut := [⟨60,201535688,201535805⟩,
⟨64,214653281,214653406⟩]
theorem checked57595 : checkPrefixCuts (2^48) 7553024001 10 Manual.Count131072.C057595.packed 64 cuts57595 = true := by
 decide +kernel
def pointBounds57595 : List (Nat × Nat × Nat) := [(7553146880,113411493142051,113411881261013)]
theorem point_links_checked57595 : (cuts57595.take 1).map (fun c => (7553024001-1+2*2^10*c.k,113411291606363+c.lower,113411679725208+c.upper)) = pointBounds57595 := by
 decide +kernel
def cuts57596 : List PrefixCut := [⟨64,215879315,215879436⟩]
theorem checked57596 : checkPrefixCuts (2^48) 7553155073 10 Manual.Count131072.C057596.packed 64 cuts57596 = true := by
 decide +kernel
def cuts57597 : List PrefixCut := [⟨48,158786083,158786175⟩,
⟨64,212558982,212559106⟩]
theorem checked57597 : checkPrefixCuts (2^48) 7553286145 10 Manual.Count131072.C057597.packed 64 cuts57597 = true := by
 decide +kernel
def pointBounds57597 : List (Nat × Nat × Nat) := [(7553384448,113411880925042,113412269044225)]
theorem point_links_checked57597 : (cuts57597.take 1).map (fun c => (7553286145-1+2*2^10*c.k,113411722138959+c.lower,113412110258050+c.upper)) = pointBounds57597 := by
 decide +kernel
def cuts57598 : List PrefixCut := [⟨64,213896818,213896937⟩]
theorem checked57598 : checkPrefixCuts (2^48) 7553417217 10 Manual.Count131072.C057598.packed 64 cuts57598 = true := by
 decide +kernel
def cuts57599 : List PrefixCut := [⟨36,119840212,119840283⟩,
⟨64,214824685,214824809⟩]
theorem checked57599 : checkPrefixCuts (2^48) 7553548289 10 Manual.Count131072.C057599.packed 64 cuts57599 = true := by
 decide +kernel
def pointBounds57599 : List (Nat × Nat × Nat) := [(7553622016,113412268434971,113412656554376)]
theorem point_links_checked57599 : (cuts57599.take 1).map (fun c => (7553548289-1+2*2^10*c.k,113412148594759+c.lower,113412536714093+c.upper)) = pointBounds57599 := by
 decide +kernel
def cuts57600 : List PrefixCut := [⟨64,217578411,217578534⟩]
theorem checked57600 : checkPrefixCuts (2^48) 7553679361 10 Manual.Count131072.C057600.packed 64 cuts57600 = true := by
 decide +kernel
def cuts57601 : List PrefixCut := [⟨24,79443682,79443729⟩,
⟨64,215152589,215152713⟩]
theorem checked57601 : checkPrefixCuts (2^48) 7553810433 10 Manual.Count131072.C057601.packed 64 cuts57601 = true := by
 decide +kernel
def pointBounds57601 : List (Nat × Nat × Nat) := [(7553859584,113412660441537,113413048561165)]
theorem point_links_checked57601 : (cuts57601.take 1).map (fun c => (7553810433-1+2*2^10*c.k,113412580997855+c.lower,113412969117436+c.upper)) = pointBounds57601 := by
 decide +kernel
def cuts57602 : List PrefixCut := [⟨64,217049233,217049358⟩]
theorem checked57602 : checkPrefixCuts (2^48) 7553941505 10 Manual.Count131072.C057602.packed 64 cuts57602 = true := by
 decide +kernel
def cuts57603 : List PrefixCut := [⟨12,39720530,39720552⟩,
⟨64,213505641,213505760⟩]
theorem checked57603 : checkPrefixCuts (2^48) 7554072577 10 Manual.Count131072.C057603.packed 64 cuts57603 = true := by
 decide +kernel
def pointBounds57603 : List (Nat × Nat × Nat) := [(7554097152,113413052920207,113413441040059)]
theorem point_links_checked57603 : (cuts57603.take 1).map (fun c => (7554072577-1+2*2^10*c.k,113413013199677+c.lower,113413401319507+c.upper)) = pointBounds57603 := by
 decide +kernel
def cuts57604 : List PrefixCut := [⟨64,212235094,212235218⟩]
theorem checked57604 : checkPrefixCuts (2^48) 7554203649 10 Manual.Count131072.C057604.packed 64 cuts57604 = true := by
 decide +kernel
def pointBounds57604 : List (Nat × Nat × Nat) := [(7554334720,113413438940412,113413827060485)]
theorem point_links_checked57604 : (cuts57604.take 1).map (fun c => (7554203649-1+2*2^10*c.k,113413226705318+c.lower,113413614825267+c.upper)) = pointBounds57604 := by
 decide +kernel
def cuts57605 : List PrefixCut := [⟨64,215063150,215063277⟩]
theorem checked57605 : checkPrefixCuts (2^48) 7554334721 10 Manual.Count131072.C057605.packed 64 cuts57605 = true := by
 decide +kernel
def cuts57606 : List PrefixCut := [⟨52,172882415,172882513⟩,
⟨64,213345491,213345612⟩]
theorem checked57606 : checkPrefixCuts (2^48) 7554465793 10 Manual.Count131072.C057606.packed 64 cuts57606 = true := by
 decide +kernel
def pointBounds57606 : List (Nat × Nat × Nat) := [(7554572288,113413826885977,113414215006275)]
theorem point_links_checked57606 : (cuts57606.take 1).map (fun c => (7554465793-1+2*2^10*c.k,113413654003562+c.lower,113414042123762+c.upper)) = pointBounds57606 := by
 decide +kernel
def cuts57607 : List PrefixCut := [⟨64,217961848,217961974⟩]
theorem checked57607 : checkPrefixCuts (2^48) 7554596865 10 Manual.Count131072.C057607.packed 64 cuts57607 = true := by
 decide +kernel
def cuts57608 : List PrefixCut := [⟨40,133606853,133606930⟩,
⟨64,215163704,215163828⟩]
theorem checked57608 : checkPrefixCuts (2^48) 7554727937 10 Manual.Count131072.C057608.packed 64 cuts57608 = true := by
 decide +kernel
def pointBounds57608 : List (Nat × Nat × Nat) := [(7554809856,113414218917754,113414607038278)]
theorem point_links_checked57608 : (cuts57608.take 1).map (fun c => (7554727937-1+2*2^10*c.k,113414085310901+c.lower,113414473431348+c.upper)) = pointBounds57608 := by
 decide +kernel
def cuts57609 : List PrefixCut := [⟨64,213818735,213818856⟩]
theorem checked57609 : checkPrefixCuts (2^48) 7554859009 10 Manual.Count131072.C057609.packed 64 cuts57609 = true := by
 decide +kernel
def cuts57610 : List PrefixCut := [⟨28,91465138,91465193⟩,
⟨64,214075799,214075925⟩]
theorem checked57610 : checkPrefixCuts (2^48) 7554990081 10 Manual.Count131072.C057610.packed 64 cuts57610 = true := by
 decide +kernel
def pointBounds57610 : List (Nat × Nat × Nat) := [(7555047424,113414605758478,113414993879225)]
theorem point_links_checked57610 : (cuts57610.take 1).map (fun c => (7554990081-1+2*2^10*c.k,113414514293340+c.lower,113414902414032+c.upper)) = pointBounds57610 := by
 decide +kernel
def cuts57611 : List PrefixCut := [⟨64,217685925,217686048⟩]
theorem checked57611 : checkPrefixCuts (2^48) 7555121153 10 Manual.Count131072.C057611.packed 64 cuts57611 = true := by
 decide +kernel
def cuts57612 : List PrefixCut := [⟨16,54132165,54132195⟩,
⟨64,215968424,215968542⟩]
theorem checked57612 : checkPrefixCuts (2^48) 7555252225 10 Manual.Count131072.C057612.packed 64 cuts57612 = true := by
 decide +kernel
def pointBounds57612 : List (Nat × Nat × Nat) := [(7555284992,113415000187229,113415388308200)]
theorem point_links_checked57612 : (cuts57612.take 1).map (fun c => (7555252225-1+2*2^10*c.k,113414946055064+c.lower,113415334176005+c.upper)) = pointBounds57612 := by
 decide +kernel
def cuts57613 : List PrefixCut := [⟨64,214176440,214176566⟩]
theorem checked57613 : checkPrefixCuts (2^48) 7555383297 10 Manual.Count131072.C057613.packed 64 cuts57613 = true := by
 decide +kernel
def cuts57614 : List PrefixCut := [⟨4,13337008,13337016⟩,
⟨64,215290337,215290460⟩]
theorem checked57614 : checkPrefixCuts (2^48) 7555514369 10 Manual.Count131072.C057614.packed 64 cuts57614 = true := by
 decide +kernel
def pointBounds57614 : List (Nat × Nat × Nat) := [(7555522560,113415389536936,113415777658129)]
theorem point_links_checked57614 : (cuts57614.take 1).map (fun c => (7555514369-1+2*2^10*c.k,113415376199928+c.lower,113415764321113+c.upper)) = pointBounds57614 := by
 decide +kernel
def cuts57615 : List PrefixCut := [⟨56,189060516,189060623⟩,
⟨64,215137603,215137725⟩]
theorem checked57615 : checkPrefixCuts (2^48) 7555645441 10 Manual.Count131072.C057615.packed 64 cuts57615 = true := by
 decide +kernel
def pointBounds57615 : List (Nat × Nat × Nat) := [(7555760128,113415780550781,113416168672196)]
theorem point_links_checked57615 : (cuts57615.take 1).map (fun c => (7555645441-1+2*2^10*c.k,113415591490265+c.lower,113415979611573+c.upper)) = pointBounds57615 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S6.B000237
