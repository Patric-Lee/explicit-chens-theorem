import PlattAssemblyKernel
import PlattCertificates.Count131072.C057616
import PlattCertificates.Count131072.C057617
import PlattCertificates.Count131072.C057618
import PlattCertificates.Count131072.C057619
import PlattCertificates.Count131072.C057620
import PlattCertificates.Count131072.C057621
import PlattCertificates.Count131072.C057622
import PlattCertificates.Count131072.C057623
import PlattCertificates.Count131072.C057624
import PlattCertificates.Count131072.C057625
import PlattCertificates.Count131072.C057626
import PlattCertificates.Count131072.C057627
import PlattCertificates.Count131072.C057628
import PlattCertificates.Count131072.C057629
import PlattCertificates.Count131072.C057630
import PlattCertificates.Count131072.C057631
import PlattCertificates.Count131072.C057632
import PlattCertificates.Count131072.C057633
import PlattCertificates.Count131072.C057634
import PlattCertificates.Count131072.C057635
import PlattCertificates.Count131072.C057636
import PlattCertificates.Count131072.C057637
import PlattCertificates.Count131072.C057638
import PlattCertificates.Count131072.C057639
import PlattCertificates.Count131072.C057640
import PlattCertificates.Count131072.C057641
import PlattCertificates.Count131072.C057642
import PlattCertificates.Count131072.C057643
import PlattCertificates.Count131072.C057644
import PlattCertificates.Count131072.C057645
import PlattCertificates.Count131072.C057646
import PlattCertificates.Count131072.C057647
namespace ChenEffective.PlattWindow.Assembly.Prefix.S6.B000238
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts57616 : List PrefixCut := [⟨64,216512207,216512331⟩]
theorem checked57616 : checkPrefixCuts (2^48) 7555776513 10 Manual.Count131072.C057616.packed 64 cuts57616 = true := by
 decide +kernel
def cuts57617 : List PrefixCut := [⟨44,149157314,149157401⟩,
⟨64,217104503,217104628⟩]
theorem checked57617 : checkPrefixCuts (2^48) 7555907585 10 Manual.Count131072.C057617.packed 64 cuts57617 = true := by
 decide +kernel
def pointBounds57617 : List (Nat × Nat × Nat) := [(7555997696,113416172297389,113416560419030)]
theorem point_links_checked57617 : (cuts57617.take 1).map (fun c => (7555907585-1+2*2^10*c.k,113416023140075+c.lower,113416411261629+c.upper)) = pointBounds57617 := by
 decide +kernel
def cuts57618 : List PrefixCut := [⟨64,217547743,217547866⟩]
theorem checked57618 : checkPrefixCuts (2^48) 7556038657 10 Manual.Count131072.C057618.packed 64 cuts57618 = true := by
 decide +kernel
def cuts57619 : List PrefixCut := [⟨32,105792388,105792451⟩,
⟨64,213260138,213260261⟩]
theorem checked57619 : checkPrefixCuts (2^48) 7556169729 10 Manual.Count131072.C057619.packed 64 cuts57619 = true := by
 decide +kernel
def pointBounds57619 : List (Nat × Nat × Nat) := [(7556235264,113416563584709,113416951706574)]
theorem point_links_checked57619 : (cuts57619.take 1).map (fun c => (7556169729-1+2*2^10*c.k,113416457792321+c.lower,113416845914123+c.upper)) = pointBounds57619 := by
 decide +kernel
def cuts57620 : List PrefixCut := [⟨64,212809431,212809555⟩]
theorem checked57620 : checkPrefixCuts (2^48) 7556300801 10 Manual.Count131072.C057620.packed 64 cuts57620 = true := by
 decide +kernel
def cuts57621 : List PrefixCut := [⟨20,66416056,66416094⟩,
⟨64,214779965,214780089⟩]
theorem checked57621 : checkPrefixCuts (2^48) 7556431873 10 Manual.Count131072.C057621.packed 64 cuts57621 = true := by
 decide +kernel
def pointBounds57621 : List (Nat × Nat × Nat) := [(7556472832,113416950277946,113417338400033)]
theorem point_links_checked57621 : (cuts57621.take 1).map (fun c => (7556431873-1+2*2^10*c.k,113416883861890+c.lower,113417271983939+c.upper)) = pointBounds57621 := by
 decide +kernel
def cuts57622 : List PrefixCut := [⟨64,212094351,212094469⟩]
theorem checked57622 : checkPrefixCuts (2^48) 7556562945 10 Manual.Count131072.C057622.packed 64 cuts57622 = true := by
 decide +kernel
def cuts57623 : List PrefixCut := [⟨8,27638296,27638311⟩,
⟨64,217379897,217380017⟩]
theorem checked57623 : checkPrefixCuts (2^48) 7556694017 10 Manual.Count131072.C057623.packed 64 cuts57623 = true := by
 decide +kernel
def pointBounds57623 : List (Nat × Nat × Nat) := [(7556710400,113417338374502,113417726496808)]
theorem point_links_checked57623 : (cuts57623.take 1).map (fun c => (7556694017-1+2*2^10*c.k,113417310736206+c.lower,113417698858497+c.upper)) = pointBounds57623 := by
 decide +kernel
def cuts57624 : List PrefixCut := [⟨60,198975981,198976098⟩,
⟨64,212422201,212422326⟩]
theorem checked57624 : checkPrefixCuts (2^48) 7556825089 10 Manual.Count131072.C057624.packed 64 cuts57624 = true := by
 decide +kernel
def pointBounds57624 : List (Nat × Nat × Nat) := [(7556947968,113417727092084,113418115214612)]
theorem point_links_checked57624 : (cuts57624.take 1).map (fun c => (7556825089-1+2*2^10*c.k,113417528116103+c.lower,113417916238514+c.upper)) = pointBounds57624 := by
 decide +kernel
def cuts57625 : List PrefixCut := [⟨64,212567507,212567625⟩]
theorem checked57625 : checkPrefixCuts (2^48) 7556956161 10 Manual.Count131072.C057625.packed 64 cuts57625 = true := by
 decide +kernel
def cuts57626 : List PrefixCut := [⟨48,160643022,160643114⟩,
⟨64,215729727,215729850⟩]
theorem checked57626 : checkPrefixCuts (2^48) 7557087233 10 Manual.Count131072.C057626.packed 64 cuts57626 = true := by
 decide +kernel
def pointBounds57626 : List (Nat × Nat × Nat) := [(7557185536,113418113748833,113418501871579)]
theorem point_links_checked57626 : (cuts57626.take 1).map (fun c => (7557087233-1+2*2^10*c.k,113417953105811+c.lower,113418341228465+c.upper)) = pointBounds57626 := by
 decide +kernel
def cuts57627 : List PrefixCut := [⟨64,213677476,213677595⟩]
theorem checked57627 : checkPrefixCuts (2^48) 7557218305 10 Manual.Count131072.C057627.packed 64 cuts57627 = true := by
 decide +kernel
def cuts57628 : List PrefixCut := [⟨36,121604945,121605016⟩,
⟨64,215349808,215349932⟩]
theorem checked57628 : checkPrefixCuts (2^48) 7557349377 10 Manual.Count131072.C057628.packed 64 cuts57628 = true := by
 decide +kernel
def pointBounds57628 : List (Nat × Nat × Nat) := [(7557423104,113418504117959,113418892240926)]
theorem point_links_checked57628 : (cuts57628.take 1).map (fun c => (7557349377-1+2*2^10*c.k,113418382513014+c.lower,113418770635910+c.upper)) = pointBounds57628 := by
 decide +kernel
def cuts57629 : List PrefixCut := [⟨64,216463387,216463512⟩]
theorem checked57629 : checkPrefixCuts (2^48) 7557480449 10 Manual.Count131072.C057629.packed 64 cuts57629 = true := by
 decide +kernel
def cuts57630 : List PrefixCut := [⟨24,82606697,82606745⟩,
⟨64,217576959,217577083⟩]
theorem checked57630 : checkPrefixCuts (2^48) 7557611521 10 Manual.Count131072.C057630.packed 64 cuts57630 = true := by
 decide +kernel
def pointBounds57630 : List (Nat × Nat × Nat) := [(7557660672,113418896932906,113419285056099)]
theorem point_links_checked57630 : (cuts57630.take 1).map (fun c => (7557611521-1+2*2^10*c.k,113418814326209+c.lower,113419202449354+c.upper)) = pointBounds57630 := by
 decide +kernel
def cuts57631 : List PrefixCut := [⟨64,215189646,215189769⟩]
theorem checked57631 : checkPrefixCuts (2^48) 7557742593 10 Manual.Count131072.C057631.packed 64 cuts57631 = true := by
 decide +kernel
def cuts57632 : List PrefixCut := [⟨12,40110221,40110242⟩,
⟨64,214515519,214515641⟩]
theorem checked57632 : checkPrefixCuts (2^48) 7557873665 10 Manual.Count131072.C057632.packed 64 cuts57632 = true := by
 decide +kernel
def pointBounds57632 : List (Nat × Nat × Nat) := [(7557898240,113419287203035,113419675326448)]
theorem point_links_checked57632 : (cuts57632.take 1).map (fun c => (7557873665-1+2*2^10*c.k,113419247092814+c.lower,113419635216206+c.upper)) = pointBounds57632 := by
 decide +kernel
def cuts57633 : List PrefixCut := [⟨64,211160065,211160184⟩]
theorem checked57633 : checkPrefixCuts (2^48) 7558004737 10 Manual.Count131072.C057633.packed 64 cuts57633 = true := by
 decide +kernel
def pointBounds57633 : List (Nat × Nat × Nat) := [(7558135808,113419672768398,113420060892031)]
theorem point_links_checked57633 : (cuts57633.take 1).map (fun c => (7558004737-1+2*2^10*c.k,113419461608333+c.lower,113419849731847+c.upper)) = pointBounds57633 := by
 decide +kernel
def cuts57634 : List PrefixCut := [⟨64,216966019,216966140⟩]
theorem checked57634 : checkPrefixCuts (2^48) 7558135809 10 Manual.Count131072.C057634.packed 64 cuts57634 = true := by
 decide +kernel
def cuts57635 : List PrefixCut := [⟨52,172832724,172832824⟩,
⟨64,213200973,213201093⟩]
theorem checked57635 : checkPrefixCuts (2^48) 7558266881 10 Manual.Count131072.C057635.packed 64 cuts57635 = true := by
 decide +kernel
def pointBounds57635 : List (Nat × Nat × Nat) := [(7558373376,113420062567141,113420450690995)]
theorem point_links_checked57635 : (cuts57635.take 1).map (fun c => (7558266881-1+2*2^10*c.k,113419889734417+c.lower,113420277858171+c.upper)) = pointBounds57635 := by
 decide +kernel
def cuts57636 : List PrefixCut := [⟨64,214649609,214649735⟩]
theorem checked57636 : checkPrefixCuts (2^48) 7558397953 10 Manual.Count131072.C057636.packed 64 cuts57636 = true := by
 decide +kernel
def cuts57637 : List PrefixCut := [⟨40,134433417,134433489⟩,
⟨64,213975604,213975721⟩]
theorem checked57637 : checkPrefixCuts (2^48) 7558529025 10 Manual.Count131072.C057637.packed 64 cuts57637 = true := by
 decide +kernel
def pointBounds57637 : List (Nat × Nat × Nat) := [(7558610944,113420452018416,113420840142488)]
theorem point_links_checked57637 : (cuts57637.take 1).map (fun c => (7558529025-1+2*2^10*c.k,113420317584999+c.lower,113420705708999+c.upper)) = pointBounds57637 := by
 decide +kernel
def cuts57638 : List PrefixCut := [⟨64,216020016,216020140⟩]
theorem checked57638 : checkPrefixCuts (2^48) 7558660097 10 Manual.Count131072.C057638.packed 64 cuts57638 = true := by
 decide +kernel
def cuts57639 : List PrefixCut := [⟨28,95403611,95403666⟩,
⟨64,217952620,217952743⟩]
theorem checked57639 : checkPrefixCuts (2^48) 7558791169 10 Manual.Count131072.C057639.packed 64 cuts57639 = true := by
 decide +kernel
def pointBounds57639 : List (Nat × Nat × Nat) := [(7558848512,113420842984230,113421231108526)]
theorem point_links_checked57639 : (cuts57639.take 1).map (fun c => (7558791169-1+2*2^10*c.k,113420747580619+c.lower,113421135704860+c.upper)) = pointBounds57639 := by
 decide +kernel
def cuts57640 : List PrefixCut := [⟨64,214969863,214969984⟩]
theorem checked57640 : checkPrefixCuts (2^48) 7558922241 10 Manual.Count131072.C057640.packed 64 cuts57640 = true := by
 decide +kernel
def cuts57641 : List PrefixCut := [⟨16,53509153,53509184⟩,
⟨64,214556528,214556648⟩]
theorem checked57641 : checkPrefixCuts (2^48) 7559053313 10 Manual.Count131072.C057641.packed 64 cuts57641 = true := by
 decide +kernel
def pointBounds57641 : List (Nat × Nat × Nat) := [(7559086080,113421234012255,113421622136771)]
theorem point_links_checked57641 : (cuts57641.take 1).map (fun c => (7559053313-1+2*2^10*c.k,113421180503102+c.lower,113421568627587+c.upper)) = pointBounds57641 := by
 decide +kernel
def cuts57642 : List PrefixCut := [⟨64,211797365,211797487⟩]
theorem checked57642 : checkPrefixCuts (2^48) 7559184385 10 Manual.Count131072.C057642.packed 64 cuts57642 = true := by
 decide +kernel
def cuts57643 : List PrefixCut := [⟨4,14559073,14559081⟩,
⟨64,213096938,213097060⟩]
theorem checked57643 : checkPrefixCuts (2^48) 7559315457 10 Manual.Count131072.C057643.packed 64 cuts57643 = true := by
 decide +kernel
def pointBounds57643 : List (Nat × Nat × Nat) := [(7559323648,113421621416068,113422009540803)]
theorem point_links_checked57643 : (cuts57643.take 1).map (fun c => (7559315457-1+2*2^10*c.k,113421606856995+c.lower,113421994981722+c.upper)) = pointBounds57643 := by
 decide +kernel
def cuts57644 : List PrefixCut := [⟨56,185577107,185577214⟩,
⟨64,213279390,213279513⟩]
theorem checked57644 : checkPrefixCuts (2^48) 7559446529 10 Manual.Count131072.C057644.packed 64 cuts57644 = true := by
 decide +kernel
def pointBounds57644 : List (Nat × Nat × Nat) := [(7559561216,113422005531040,113422393655996)]
theorem point_links_checked57644 : (cuts57644.take 1).map (fun c => (7559446529-1+2*2^10*c.k,113421819953933+c.lower,113422208078782+c.upper)) = pointBounds57644 := by
 decide +kernel
def cuts57645 : List PrefixCut := [⟨64,216775685,216775805⟩]
theorem checked57645 : checkPrefixCuts (2^48) 7559577601 10 Manual.Count131072.C057645.packed 64 cuts57645 = true := by
 decide +kernel
def cuts57646 : List PrefixCut := [⟨44,145880238,145880322⟩,
⟨64,212787971,212788093⟩]
theorem checked57646 : checkPrefixCuts (2^48) 7559708673 10 Manual.Count131072.C057646.packed 64 cuts57646 = true := by
 decide +kernel
def pointBounds57646 : List (Nat × Nat × Nat) := [(7559798784,113422395889246,113422784014422)]
theorem point_links_checked57646 : (cuts57646.take 1).map (fun c => (7559708673-1+2*2^10*c.k,113422250009008+c.lower,113422638134100+c.upper)) = pointBounds57646 := by
 decide +kernel
def cuts57647 : List PrefixCut := [⟨64,214794848,214794971⟩]
theorem checked57647 : checkPrefixCuts (2^48) 7559839745 10 Manual.Count131072.C057647.packed 64 cuts57647 = true := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S6.B000238
