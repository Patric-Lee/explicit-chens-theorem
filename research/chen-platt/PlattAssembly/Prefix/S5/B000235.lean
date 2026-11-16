import PlattAssemblyKernel
import PlattCertificates.Count131072.C047520
import PlattCertificates.Count131072.C047521
import PlattCertificates.Count131072.C047522
import PlattCertificates.Count131072.C047523
import PlattCertificates.Count131072.C047524
import PlattCertificates.Count131072.C047525
import PlattCertificates.Count131072.C047526
import PlattCertificates.Count131072.C047527
import PlattCertificates.Count131072.C047528
import PlattCertificates.Count131072.C047529
import PlattCertificates.Count131072.C047530
import PlattCertificates.Count131072.C047531
import PlattCertificates.Count131072.C047532
import PlattCertificates.Count131072.C047533
import PlattCertificates.Count131072.C047534
import PlattCertificates.Count131072.C047535
import PlattCertificates.Count131072.C047536
import PlattCertificates.Count131072.C047537
import PlattCertificates.Count131072.C047538
import PlattCertificates.Count131072.C047539
import PlattCertificates.Count131072.C047540
import PlattCertificates.Count131072.C047541
import PlattCertificates.Count131072.C047542
import PlattCertificates.Count131072.C047543
import PlattCertificates.Count131072.C047544
import PlattCertificates.Count131072.C047545
import PlattCertificates.Count131072.C047546
import PlattCertificates.Count131072.C047547
import PlattCertificates.Count131072.C047548
import PlattCertificates.Count131072.C047549
import PlattCertificates.Count131072.C047550
import PlattCertificates.Count131072.C047551
namespace ChenEffective.PlattWindow.Assembly.Prefix.S5.B000235
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts47520 : List PrefixCut := [⟨64,266727679,266727833⟩]
theorem checked47520 : checkPrefixCuts (2^48) 6232473601 10 Manual.Count131072.C047520.packed 64 cuts47520 = true := by
 decide +kernel
def cuts47521 : List PrefixCut := [⟨16,66252010,66252046⟩,
⟨64,262522080,262522232⟩]
theorem checked47521 : checkPrefixCuts (2^48) 6232604673 10 Manual.Count131072.C047521.packed 64 cuts47521 = true := by
 decide +kernel
def pointBounds47521 : List (Nat × Nat × Nat) := [(6232637440,111023410768180,111023797528458)]
theorem point_links_checked47521 : (cuts47521.take 1).map (fun c => (6232604673-1+2*2^10*c.k,111023344516170+c.lower,111023731276412+c.upper)) = pointBounds47521 := by
 decide +kernel
def cuts47522 : List PrefixCut := [⟨48,199744335,199744449⟩,
⟨64,266084226,266084379⟩]
theorem checked47522 : checkPrefixCuts (2^48) 6232735745 10 Manual.Count131072.C047522.packed 64 cuts47522 = true := by
 decide +kernel
def pointBounds47522 : List (Nat × Nat × Nat) := [(6232834048,111023806782585,111024193543093)]
theorem point_links_checked47522 : (cuts47522.take 1).map (fun c => (6232735745-1+2*2^10*c.k,111023607038250+c.lower,111023993798644+c.upper)) = pointBounds47522 := by
 decide +kernel
def cuts47523 : List PrefixCut := [⟨64,257453202,257453351⟩]
theorem checked47523 : checkPrefixCuts (2^48) 6232866817 10 Manual.Count131072.C047523.packed 64 cuts47523 = true := by
 decide +kernel
def cuts47524 : List PrefixCut := [⟨16,64396321,64396357⟩,
⟨64,261512025,261512173⟩]
theorem checked47524 : checkPrefixCuts (2^48) 6232997889 10 Manual.Count131072.C047524.packed 64 cuts47524 = true := by
 decide +kernel
def pointBounds47524 : List (Nat × Nat × Nat) := [(6233030656,111024194971999,111024581732731)]
theorem point_links_checked47524 : (cuts47524.take 1).map (fun c => (6232997889-1+2*2^10*c.k,111024130575678+c.lower,111024517336374+c.upper)) = pointBounds47524 := by
 decide +kernel
def cuts47525 : List PrefixCut := [⟨48,194448310,194448422⟩,
⟨64,260693700,260693850⟩]
theorem checked47525 : checkPrefixCuts (2^48) 6233128961 10 Manual.Count131072.C047525.packed 64 cuts47525 = true := by
 decide +kernel
def pointBounds47525 : List (Nat × Nat × Nat) := [(6233227264,111024586536013,111024973296969)]
theorem point_links_checked47525 : (cuts47525.take 1).map (fun c => (6233128961-1+2*2^10*c.k,111024392087703+c.lower,111024778848547+c.upper)) = pointBounds47525 := by
 decide +kernel
def cuts47526 : List PrefixCut := [⟨64,263036369,263036514⟩]
theorem checked47526 : checkPrefixCuts (2^48) 6233260033 10 Manual.Count131072.C047526.packed 64 cuts47526 = true := by
 decide +kernel
def cuts47527 : List PrefixCut := [⟨16,65837245,65837286⟩,
⟨64,265017665,265017820⟩]
theorem checked47527 : checkPrefixCuts (2^48) 6233391105 10 Manual.Count131072.C047527.packed 64 cuts47527 = true := by
 decide +kernel
def pointBounds47527 : List (Nat × Nat × Nat) := [(6233423872,111024981655017,111025368416197)]
theorem point_links_checked47527 : (cuts47527.take 1).map (fun c => (6233391105-1+2*2^10*c.k,111024915817772+c.lower,111025302578911+c.upper)) = pointBounds47527 := by
 decide +kernel
def cuts47528 : List PrefixCut := [⟨48,198274181,198274296⟩,
⟨64,263657465,263657617⟩]
theorem checked47528 : checkPrefixCuts (2^48) 6233522177 10 Manual.Count131072.C047528.packed 64 cuts47528 = true := by
 decide +kernel
def pointBounds47528 : List (Nat × Nat × Nat) := [(6233620480,111025379109618,111025765871027)]
theorem point_links_checked47528 : (cuts47528.take 1).map (fun c => (6233522177-1+2*2^10*c.k,111025180835437+c.lower,111025567596731+c.upper)) = pointBounds47528 := by
 decide +kernel
def cuts47529 : List PrefixCut := [⟨64,263787365,263787512⟩]
theorem checked47529 : checkPrefixCuts (2^48) 6233653249 10 Manual.Count131072.C047529.packed 64 cuts47529 = true := by
 decide +kernel
def cuts47530 : List PrefixCut := [⟨16,65155798,65155836⟩,
⟨64,257415318,257415468⟩]
theorem checked47530 : checkPrefixCuts (2^48) 6233784321 10 Manual.Count131072.C047530.packed 64 cuts47530 = true := by
 decide +kernel
def pointBounds47530 : List (Nat × Nat × Nat) := [(6233817088,111025773436065,111026160197696)]
theorem point_links_checked47530 : (cuts47530.take 1).map (fun c => (6233784321-1+2*2^10*c.k,111025708280267+c.lower,111026095041860+c.upper)) = pointBounds47530 := by
 decide +kernel
def cuts47531 : List PrefixCut := [⟨48,199164695,199164809⟩,
⟨64,265356579,265356733⟩]
theorem checked47531 : checkPrefixCuts (2^48) 6233915393 10 Manual.Count131072.C047531.packed 64 cuts47531 = true := by
 decide +kernel
def pointBounds47531 : List (Nat × Nat × Nat) := [(6234013696,111026164860280,111026551622137)]
theorem point_links_checked47531 : (cuts47531.take 1).map (fun c => (6233915393-1+2*2^10*c.k,111025965695585+c.lower,111026352457328+c.upper)) = pointBounds47531 := by
 decide +kernel
def cuts47532 : List PrefixCut := [⟨64,265667071,265667224⟩]
theorem checked47532 : checkPrefixCuts (2^48) 6234046465 10 Manual.Count131072.C047532.packed 64 cuts47532 = true := by
 decide +kernel
def cuts47533 : List PrefixCut := [⟨16,65558043,65558079⟩,
⟨64,264171543,264171692⟩]
theorem checked47533 : checkPrefixCuts (2^48) 6234177537 10 Manual.Count131072.C047533.packed 64 cuts47533 = true := by
 decide +kernel
def pointBounds47533 : List (Nat × Nat × Nat) := [(6234210304,111026562277278,111026949039364)]
theorem point_links_checked47533 : (cuts47533.take 1).map (fun c => (6234177537-1+2*2^10*c.k,111026496719235+c.lower,111026883481285+c.upper)) = pointBounds47533 := by
 decide +kernel
def cuts47534 : List PrefixCut := [⟨48,191883169,191883276⟩,
⟨64,256355237,256355380⟩]
theorem checked47534 : checkPrefixCuts (2^48) 6234308609 10 Manual.Count131072.C047534.packed 64 cuts47534 = true := by
 decide +kernel
def pointBounds47534 : List (Nat × Nat × Nat) := [(6234406912,111026952773947,111027339536253)]
theorem point_links_checked47534 : (cuts47534.take 1).map (fun c => (6234308609-1+2*2^10*c.k,111026760890778+c.lower,111027147652977+c.upper)) = pointBounds47534 := by
 decide +kernel
def cuts47535 : List PrefixCut := [⟨64,262941429,262941580⟩]
theorem checked47535 : checkPrefixCuts (2^48) 6234439681 10 Manual.Count131072.C047535.packed 64 cuts47535 = true := by
 decide +kernel
def cuts47536 : List PrefixCut := [⟨16,65012135,65012173⟩,
⟨64,261762089,261762241⟩]
theorem checked47536 : checkPrefixCuts (2^48) 6234570753 10 Manual.Count131072.C047536.packed 64 cuts47536 = true := by
 decide +kernel
def pointBounds47536 : List (Nat × Nat × Nat) := [(6234603520,111027345199579,111027731962110)]
theorem point_links_checked47536 : (cuts47536.take 1).map (fun c => (6234570753-1+2*2^10*c.k,111027280187444+c.lower,111027666949937+c.upper)) = pointBounds47536 := by
 decide +kernel
def cuts47537 : List PrefixCut := [⟨48,196656568,196656677⟩,
⟨64,263336702,263336847⟩]
theorem checked47537 : checkPrefixCuts (2^48) 6234701825 10 Manual.Count131072.C047537.packed 64 cuts47537 = true := by
 decide +kernel
def pointBounds47537 : List (Nat × Nat × Nat) := [(6234800128,111027738606101,111028125368855)]
theorem point_links_checked47537 : (cuts47537.take 1).map (fun c => (6234701825-1+2*2^10*c.k,111027541949533+c.lower,111027928712178+c.upper)) = pointBounds47537 := by
 decide +kernel
def cuts47538 : List PrefixCut := [⟨64,259855004,259855156⟩]
theorem checked47538 : checkPrefixCuts (2^48) 6234832897 10 Manual.Count131072.C047538.packed 64 cuts47538 = true := by
 decide +kernel
def cuts47539 : List PrefixCut := [⟨16,65956077,65956110⟩,
⟨64,265492553,265492700⟩]
theorem checked47539 : checkPrefixCuts (2^48) 6234963969 10 Manual.Count131072.C047539.packed 64 cuts47539 = true := by
 decide +kernel
def pointBounds47539 : List (Nat × Nat × Nat) := [(6234996736,111028131097316,111028517860291)]
theorem point_links_checked47539 : (cuts47539.take 1).map (fun c => (6234963969-1+2*2^10*c.k,111028065141239+c.lower,111028451904181+c.upper)) = pointBounds47539 := by
 decide +kernel
def cuts47540 : List PrefixCut := [⟨48,197682442,197682552⟩,
⟨64,263184661,263184808⟩]
theorem checked47540 : checkPrefixCuts (2^48) 6235095041 10 Manual.Count131072.C047540.packed 64 cuts47540 = true := by
 decide +kernel
def pointBounds47540 : List (Nat × Nat × Nat) := [(6235193344,111028528316234,111028915079433)]
theorem point_links_checked47540 : (cuts47540.take 1).map (fun c => (6235095041-1+2*2^10*c.k,111028330633792+c.lower,111028717396881+c.upper)) = pointBounds47540 := by
 decide +kernel
def cuts47541 : List PrefixCut := [⟨64,262050586,262050730⟩]
theorem checked47541 : checkPrefixCuts (2^48) 6235226113 10 Manual.Count131072.C047541.packed 64 cuts47541 = true := by
 decide +kernel
def cuts47542 : List PrefixCut := [⟨16,65410218,65410254⟩,
⟨64,260510259,260510407⟩]
theorem checked47542 : checkPrefixCuts (2^48) 6235357185 10 Manual.Count131072.C047542.packed 64 cuts47542 = true := by
 decide +kernel
def pointBounds47542 : List (Nat × Nat × Nat) := [(6235389952,111028921279257,111029308042673)]
theorem point_links_checked47542 : (cuts47542.take 1).map (fun c => (6235357185-1+2*2^10*c.k,111028855869039+c.lower,111029242632419+c.upper)) = pointBounds47542 := by
 decide +kernel
def cuts47543 : List PrefixCut := [⟨48,196902602,196902716⟩,
⟨64,261407613,261407764⟩]
theorem checked47543 : checkPrefixCuts (2^48) 6235488257 10 Manual.Count131072.C047543.packed 64 cuts47543 = true := by
 decide +kernel
def pointBounds47543 : List (Nat × Nat × Nat) := [(6235586560,111029313281900,111029700045542)]
theorem point_links_checked47543 : (cuts47543.take 1).map (fun c => (6235488257-1+2*2^10*c.k,111029116379298+c.lower,111029503142826+c.upper)) = pointBounds47543 := by
 decide +kernel
def cuts47544 : List PrefixCut := [⟨64,262395164,262395319⟩]
theorem checked47544 : checkPrefixCuts (2^48) 6235619329 10 Manual.Count131072.C047544.packed 64 cuts47544 = true := by
 decide +kernel
def cuts47545 : List PrefixCut := [⟨16,67437332,67437370⟩,
⟨64,265504215,265504370⟩]
theorem checked47545 : checkPrefixCuts (2^48) 6235750401 10 Manual.Count131072.C047545.packed 64 cuts47545 = true := by
 decide +kernel
def pointBounds47545 : List (Nat × Nat × Nat) := [(6235783168,111029707619407,111030094383279)]
theorem point_links_checked47545 : (cuts47545.take 1).map (fun c => (6235750401-1+2*2^10*c.k,111029640182075+c.lower,111030026945909+c.upper)) = pointBounds47545 := by
 decide +kernel
def cuts47546 : List PrefixCut := [⟨48,197206155,197206268⟩,
⟨64,262564700,262564851⟩]
theorem checked47546 : checkPrefixCuts (2^48) 6235881473 10 Manual.Count131072.C047546.packed 64 cuts47546 = true := by
 decide +kernel
def pointBounds47546 : List (Nat × Nat × Nat) := [(6235979776,111030102892445,111030489656547)]
theorem point_links_checked47546 : (cuts47546.take 1).map (fun c => (6235881473-1+2*2^10*c.k,111029905686290+c.lower,111030292450279+c.upper)) = pointBounds47546 := by
 decide +kernel
def cuts47547 : List PrefixCut := [⟨64,263326486,263326631⟩]
theorem checked47547 : checkPrefixCuts (2^48) 6236012545 10 Manual.Count131072.C047547.packed 64 cuts47547 = true := by
 decide +kernel
def cuts47548 : List PrefixCut := [⟨16,65311693,65311731⟩,
⟨64,260973904,260974050⟩]
theorem checked47548 : checkPrefixCuts (2^48) 6236143617 10 Manual.Count131072.C047548.packed 64 cuts47548 = true := by
 decide +kernel
def pointBounds47548 : List (Nat × Nat × Nat) := [(6236176384,111030496889169,111030883653492)]
theorem point_links_checked47548 : (cuts47548.take 1).map (fun c => (6236143617-1+2*2^10*c.k,111030431577476+c.lower,111030818341761+c.upper)) = pointBounds47548 := by
 decide +kernel
def cuts47549 : List PrefixCut := [⟨48,198908833,198908946⟩,
⟨64,263857052,263857203⟩]
theorem checked47549 : checkPrefixCuts (2^48) 6236274689 10 Manual.Count131072.C047549.packed 64 cuts47549 = true := by
 decide +kernel
def pointBounds47549 : List (Nat × Nat × Nat) := [(6236372992,111030891460213,111031278224757)]
theorem point_links_checked47549 : (cuts47549.take 1).map (fun c => (6236274689-1+2*2^10*c.k,111030692551380+c.lower,111031079315811+c.upper)) = pointBounds47549 := by
 decide +kernel
def cuts47550 : List PrefixCut := [⟨64,262948808,262948954⟩]
theorem checked47550 : checkPrefixCuts (2^48) 6236405761 10 Manual.Count131072.C047550.packed 64 cuts47550 = true := by
 decide +kernel
def cuts47551 : List PrefixCut := [⟨16,65849175,65849212⟩,
⟨64,263123812,263123958⟩]
theorem checked47551 : checkPrefixCuts (2^48) 6236536833 10 Manual.Count131072.C047551.packed 64 cuts47551 = true := by
 decide +kernel
def pointBounds47551 : List (Nat × Nat × Nat) := [(6236569600,111031285206415,111031671971180)]
theorem point_links_checked47551 : (cuts47551.take 1).map (fun c => (6236536833-1+2*2^10*c.k,111031219357240+c.lower,111031606121968+c.upper)) = pointBounds47551 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S5.B000235
