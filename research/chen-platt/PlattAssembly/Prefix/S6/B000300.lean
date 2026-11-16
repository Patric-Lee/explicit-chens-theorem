import PlattAssemblyKernel
import PlattCertificates.Count131072.C059600
import PlattCertificates.Count131072.C059601
import PlattCertificates.Count131072.C059602
import PlattCertificates.Count131072.C059603
import PlattCertificates.Count131072.C059604
import PlattCertificates.Count131072.C059605
import PlattCertificates.Count131072.C059606
import PlattCertificates.Count131072.C059607
import PlattCertificates.Count131072.C059608
import PlattCertificates.Count131072.C059609
import PlattCertificates.Count131072.C059610
import PlattCertificates.Count131072.C059611
import PlattCertificates.Count131072.C059612
import PlattCertificates.Count131072.C059613
import PlattCertificates.Count131072.C059614
import PlattCertificates.Count131072.C059615
import PlattCertificates.Count131072.C059616
import PlattCertificates.Count131072.C059617
import PlattCertificates.Count131072.C059618
import PlattCertificates.Count131072.C059619
import PlattCertificates.Count131072.C059620
import PlattCertificates.Count131072.C059621
import PlattCertificates.Count131072.C059622
import PlattCertificates.Count131072.C059623
import PlattCertificates.Count131072.C059624
import PlattCertificates.Count131072.C059625
import PlattCertificates.Count131072.C059626
import PlattCertificates.Count131072.C059627
import PlattCertificates.Count131072.C059628
import PlattCertificates.Count131072.C059629
import PlattCertificates.Count131072.C059630
import PlattCertificates.Count131072.C059631
namespace ChenEffective.PlattWindow.Assembly.Prefix.S6.B000300
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts59600 : List PrefixCut := [⟨64,211829434,211829550⟩]
theorem checked59600 : checkPrefixCuts (2^48) 7815823361 10 Manual.Count131072.C059600.packed 64 cuts59600 = true := by
 decide +kernel
def cuts59601 : List PrefixCut := [⟨15,49949743,49949771⟩,
⟨64,207504378,207504498⟩]
theorem checked59601 : checkPrefixCuts (2^48) 7815954433 10 Manual.Count131072.C059601.packed 64 cuts59601 = true := by
 decide +kernel
def pointBounds59601 : List (Nat × Nat × Nat) := [(7815985152,113834426903201,113834815263423)]
theorem point_links_checked59601 : (cuts59601.take 1).map (fun c => (7815954433-1+2*2^10*c.k,113834376953458+c.lower,113834765313652+c.upper)) = pointBounds59601 := by
 decide +kernel
def cuts59602 : List PrefixCut := [⟨64,209193444,209193563⟩]
theorem checked59602 : checkPrefixCuts (2^48) 7816085505 10 Manual.Count131072.C059602.packed 64 cuts59602 = true := by
 decide +kernel
def cuts59603 : List PrefixCut := [⟨7,22687322,22687334⟩,
⟨64,207029272,207029387⟩]
theorem checked59603 : checkPrefixCuts (2^48) 7816216577 10 Manual.Count131072.C059603.packed 64 cuts59603 = true := by
 decide +kernel
def pointBounds59603 : List (Nat × Nat × Nat) := [(7816230912,113834816338602,113835204699047)]
theorem point_links_checked59603 : (cuts59603.take 1).map (fun c => (7816216577-1+2*2^10*c.k,113834793651280+c.lower,113835182011713+c.upper)) = pointBounds59603 := by
 decide +kernel
def cuts59604 : List PrefixCut := [⟨63,204108953,204109069⟩,
⟨64,207529946,207530064⟩]
theorem checked59604 : checkPrefixCuts (2^48) 7816347649 10 Manual.Count131072.C059604.packed 64 cuts59604 = true := by
 decide +kernel
def pointBounds59604 : List (Nat × Nat × Nat) := [(7816476672,113835204789505,113835593150169)]
theorem point_links_checked59604 : (cuts59604.take 1).map (fun c => (7816347649-1+2*2^10*c.k,113835000680552+c.lower,113835389041100+c.upper)) = pointBounds59604 := by
 decide +kernel
def cuts59605 : List PrefixCut := [⟨64,208426719,208426837⟩]
theorem checked59605 : checkPrefixCuts (2^48) 7816478721 10 Manual.Count131072.C059605.packed 64 cuts59605 = true := by
 decide +kernel
def cuts59606 : List PrefixCut := [⟨55,176518988,176519089⟩,
⟨64,205038340,205038457⟩]
theorem checked59606 : checkPrefixCuts (2^48) 7816609793 10 Manual.Count131072.C059606.packed 64 cuts59606 = true := by
 decide +kernel
def pointBounds59606 : List (Nat × Nat × Nat) := [(7816722432,113835593156205,113835981517090)]
theorem point_links_checked59606 : (cuts59606.take 1).map (fun c => (7816609793-1+2*2^10*c.k,113835416637217+c.lower,113835804998001+c.upper)) = pointBounds59606 := by
 decide +kernel
def cuts59607 : List PrefixCut := [⟨64,206655281,206655401⟩]
theorem checked59607 : checkPrefixCuts (2^48) 7816740865 10 Manual.Count131072.C059607.packed 64 cuts59607 = true := by
 decide +kernel
def cuts59608 : List PrefixCut := [⟨47,147670508,147670597⟩,
⟨64,203447074,203447194⟩]
theorem checked59608 : checkPrefixCuts (2^48) 7816871937 10 Manual.Count131072.C059608.packed 64 cuts59608 = true := by
 decide +kernel
def pointBounds59608 : List (Nat × Nat × Nat) := [(7816968192,113835976001346,113836364362456)]
theorem point_links_checked59608 : (cuts59608.take 1).map (fun c => (7816871937-1+2*2^10*c.k,113835828330838+c.lower,113836216691859+c.upper)) = pointBounds59608 := by
 decide +kernel
def cuts59609 : List PrefixCut := [⟨64,208520788,208520903⟩]
theorem checked59609 : checkPrefixCuts (2^48) 7817003009 10 Manual.Count131072.C059609.packed 64 cuts59609 = true := by
 decide +kernel
def cuts59610 : List PrefixCut := [⟨39,128293811,128293884⟩,
⟨64,210317628,210317747⟩]
theorem checked59610 : checkPrefixCuts (2^48) 7817134081 10 Manual.Count131072.C059610.packed 64 cuts59610 = true := by
 decide +kernel
def pointBounds59610 : List (Nat × Nat × Nat) := [(7817213952,113836368592511,113836756953840)]
theorem point_links_checked59610 : (cuts59610.take 1).map (fun c => (7817134081-1+2*2^10*c.k,113836240298700+c.lower,113836628659956+c.upper)) = pointBounds59610 := by
 decide +kernel
def cuts59611 : List PrefixCut := [⟨64,206641429,206641543⟩]
theorem checked59611 : checkPrefixCuts (2^48) 7817265153 10 Manual.Count131072.C059611.packed 64 cuts59611 = true := by
 decide +kernel
def cuts59612 : List PrefixCut := [⟨31,100312927,100312983⟩,
⟨64,205809842,205809959⟩]
theorem checked59612 : checkPrefixCuts (2^48) 7817396225 10 Manual.Count131072.C059612.packed 64 cuts59612 = true := by
 decide +kernel
def pointBounds59612 : List (Nat × Nat × Nat) := [(7817459712,113836757570684,113837145932229)]
theorem point_links_checked59612 : (cuts59612.take 1).map (fun c => (7817396225-1+2*2^10*c.k,113836657257757+c.lower,113837045619246+c.upper)) = pointBounds59612 := by
 decide +kernel
def cuts59613 : List PrefixCut := [⟨64,210271046,210271164⟩]
theorem checked59613 : checkPrefixCuts (2^48) 7817527297 10 Manual.Count131072.C059613.packed 64 cuts59613 = true := by
 decide +kernel
def cuts59614 : List PrefixCut := [⟨23,73954075,73954117⟩,
⟨64,205154849,205154966⟩]
theorem checked59614 : checkPrefixCuts (2^48) 7817658369 10 Manual.Count131072.C059614.packed 64 cuts59614 = true := by
 decide +kernel
def pointBounds59614 : List (Nat × Nat × Nat) := [(7817705472,113837147292720,113837535654486)]
theorem point_links_checked59614 : (cuts59614.take 1).map (fun c => (7817658369-1+2*2^10*c.k,113837073338645+c.lower,113837461700369+c.upper)) = pointBounds59614 := by
 decide +kernel
def cuts59615 : List PrefixCut := [⟨64,205583451,205583568⟩]
theorem checked59615 : checkPrefixCuts (2^48) 7817789441 10 Manual.Count131072.C059615.packed 64 cuts59615 = true := by
 decide +kernel
def cuts59616 : List PrefixCut := [⟨15,46912868,46912895⟩,
⟨64,204967947,204968062⟩]
theorem checked59616 : checkPrefixCuts (2^48) 7817920513 10 Manual.Count131072.C059616.packed 64 cuts59616 = true := by
 decide +kernel
def pointBounds59616 : List (Nat × Nat × Nat) := [(7817951232,113837530989813,113837919351798)]
theorem point_links_checked59616 : (cuts59616.take 1).map (fun c => (7817920513-1+2*2^10*c.k,113837484076945+c.lower,113837872438903+c.upper)) = pointBounds59616 := by
 decide +kernel
def cuts59617 : List PrefixCut := [⟨64,206296630,206296751⟩]
theorem checked59617 : checkPrefixCuts (2^48) 7818051585 10 Manual.Count131072.C059617.packed 64 cuts59617 = true := by
 decide +kernel
def cuts59618 : List PrefixCut := [⟨7,22393596,22393610⟩,
⟨64,206617207,206617325⟩]
theorem checked59618 : checkPrefixCuts (2^48) 7818182657 10 Manual.Count131072.C059618.packed 64 cuts59618 = true := by
 decide +kernel
def pointBounds59618 : List (Nat × Nat × Nat) := [(7818196992,113837917735118,113838306097326)]
theorem point_links_checked59618 : (cuts59618.take 1).map (fun c => (7818182657-1+2*2^10*c.k,113837895341522+c.lower,113838283703716+c.upper)) = pointBounds59618 := by
 decide +kernel
def cuts59619 : List PrefixCut := [⟨63,205317673,205317781⟩,
⟨64,208881811,208881921⟩]
theorem checked59619 : checkPrefixCuts (2^48) 7818313729 10 Manual.Count131072.C059619.packed 64 cuts59619 = true := by
 decide +kernel
def pointBounds59619 : List (Nat × Nat × Nat) := [(7818442752,113838307276402,113838695638822)]
theorem point_links_checked59619 : (cuts59619.take 1).map (fun c => (7818313729-1+2*2^10*c.k,113838101958729+c.lower,113838490321041+c.upper)) = pointBounds59619 := by
 decide +kernel
def cuts59620 : List PrefixCut := [⟨64,206646245,206646360⟩]
theorem checked59620 : checkPrefixCuts (2^48) 7818444801 10 Manual.Count131072.C059620.packed 64 cuts59620 = true := by
 decide +kernel
def cuts59621 : List PrefixCut := [⟨55,178922638,178922744⟩,
⟨64,208658827,208658950⟩]
theorem checked59621 : checkPrefixCuts (2^48) 7818575873 10 Manual.Count131072.C059621.packed 64 cuts59621 = true := by
 decide +kernel
def pointBounds59621 : List (Nat × Nat × Nat) := [(7818688512,113838696409423,113839084772066)]
theorem point_links_checked59621 : (cuts59621.take 1).map (fun c => (7818575873-1+2*2^10*c.k,113838517486785+c.lower,113838905849322+c.upper)) = pointBounds59621 := by
 decide +kernel
def cuts59622 : List PrefixCut := [⟨64,209303350,209303460⟩]
theorem checked59622 : checkPrefixCuts (2^48) 7818706945 10 Manual.Count131072.C059622.packed 64 cuts59622 = true := by
 decide +kernel
def cuts59623 : List PrefixCut := [⟨47,153069280,153069369⟩,
⟨64,206491883,206492003⟩]
theorem checked59623 : checkPrefixCuts (2^48) 7818838017 10 Manual.Count131072.C059623.packed 64 cuts59623 = true := by
 decide +kernel
def pointBounds59623 : List (Nat × Nat × Nat) := [(7818934272,113839088518242,113839476881101)]
theorem point_links_checked59623 : (cuts59623.take 1).map (fun c => (7818838017-1+2*2^10*c.k,113838935448962+c.lower,113839323811732+c.upper)) = pointBounds59623 := by
 decide +kernel
def cuts59624 : List PrefixCut := [⟨64,207532382,207532501⟩]
theorem checked59624 : checkPrefixCuts (2^48) 7818969089 10 Manual.Count131072.C059624.packed 64 cuts59624 = true := by
 decide +kernel
def cuts59625 : List PrefixCut := [⟨39,127397602,127397676⟩,
⟨64,206700947,206701069⟩]
theorem checked59625 : checkPrefixCuts (2^48) 7819100161 10 Manual.Count131072.C059625.packed 64 cuts59625 = true := by
 decide +kernel
def pointBounds59625 : List (Nat × Nat × Nat) := [(7819180032,113839476870829,113839865233912)]
theorem point_links_checked59625 : (cuts59625.take 1).map (fun c => (7819100161-1+2*2^10*c.k,113839349473227+c.lower,113839737836236+c.upper)) = pointBounds59625 := by
 decide +kernel
def cuts59626 : List PrefixCut := [⟨64,206985447,206985567⟩]
theorem checked59626 : checkPrefixCuts (2^48) 7819231233 10 Manual.Count131072.C059626.packed 64 cuts59626 = true := by
 decide +kernel
def cuts59627 : List PrefixCut := [⟨31,101763579,101763640⟩,
⟨64,209969718,209969840⟩]
theorem checked59627 : checkPrefixCuts (2^48) 7819362305 10 Manual.Count131072.C059627.packed 64 cuts59627 = true := by
 decide +kernel
def pointBounds59627 : List (Nat × Nat × Nat) := [(7819425792,113839864923200,113840253286512)]
theorem point_links_checked59627 : (cuts59627.take 1).map (fun c => (7819362305-1+2*2^10*c.k,113839763159621+c.lower,113840151522872+c.upper)) = pointBounds59627 := by
 decide +kernel
def cuts59628 : List PrefixCut := [⟨64,206222595,206222713⟩]
theorem checked59628 : checkPrefixCuts (2^48) 7819493377 10 Manual.Count131072.C059628.packed 64 cuts59628 = true := by
 decide +kernel
def cuts59629 : List PrefixCut := [⟨23,75339316,75339358⟩,
⟨64,206867063,206867181⟩]
theorem checked59629 : checkPrefixCuts (2^48) 7819624449 10 Manual.Count131072.C059629.packed 64 cuts59629 = true := by
 decide +kernel
def pointBounds59629 : List (Nat × Nat × Nat) := [(7819671552,113840254691250,113840643054783)]
theorem point_links_checked59629 : (cuts59629.take 1).map (fun c => (7819624449-1+2*2^10*c.k,113840179351934+c.lower,113840567715425+c.upper)) = pointBounds59629 := by
 decide +kernel
def cuts59630 : List PrefixCut := [⟨64,208411380,208411502⟩]
theorem checked59630 : checkPrefixCuts (2^48) 7819755521 10 Manual.Count131072.C059630.packed 64 cuts59630 = true := by
 decide +kernel
def cuts59631 : List PrefixCut := [⟨15,47728953,47728976⟩,
⟨64,204952406,204952524⟩]
theorem checked59631 : checkPrefixCuts (2^48) 7819886593 10 Manual.Count131072.C059631.packed 64 cuts59631 = true := by
 decide +kernel
def pointBounds59631 : List (Nat × Nat × Nat) := [(7819917312,113840642359330,113841030723084)]
theorem point_links_checked59631 : (cuts59631.take 1).map (fun c => (7819886593-1+2*2^10*c.k,113840594630377+c.lower,113840982994108+c.upper)) = pointBounds59631 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S6.B000300
