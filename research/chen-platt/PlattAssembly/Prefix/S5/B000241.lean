import PlattAssemblyKernel
import PlattCertificates.Count131072.C047712
import PlattCertificates.Count131072.C047713
import PlattCertificates.Count131072.C047714
import PlattCertificates.Count131072.C047715
import PlattCertificates.Count131072.C047716
import PlattCertificates.Count131072.C047717
import PlattCertificates.Count131072.C047718
import PlattCertificates.Count131072.C047719
import PlattCertificates.Count131072.C047720
import PlattCertificates.Count131072.C047721
import PlattCertificates.Count131072.C047722
import PlattCertificates.Count131072.C047723
import PlattCertificates.Count131072.C047724
import PlattCertificates.Count131072.C047725
import PlattCertificates.Count131072.C047726
import PlattCertificates.Count131072.C047727
import PlattCertificates.Count131072.C047728
import PlattCertificates.Count131072.C047729
import PlattCertificates.Count131072.C047730
import PlattCertificates.Count131072.C047731
import PlattCertificates.Count131072.C047732
import PlattCertificates.Count131072.C047733
import PlattCertificates.Count131072.C047734
import PlattCertificates.Count131072.C047735
import PlattCertificates.Count131072.C047736
import PlattCertificates.Count131072.C047737
import PlattCertificates.Count131072.C047738
import PlattCertificates.Count131072.C047739
import PlattCertificates.Count131072.C047740
import PlattCertificates.Count131072.C047741
import PlattCertificates.Count131072.C047742
import PlattCertificates.Count131072.C047743
namespace ChenEffective.PlattWindow.Assembly.Prefix.S5.B000241
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts47712 : List PrefixCut := [⟨64,261561810,261561962⟩]
theorem checked47712 : checkPrefixCuts (2^48) 6257639425 10 Manual.Count131072.C047712.packed 64 cuts47712 = true := by
 decide +kernel
def cuts47713 : List PrefixCut := [⟨16,66345413,66345452⟩,
⟨64,260521795,260521943⟩]
theorem checked47713 : checkPrefixCuts (2^48) 6257770497 10 Manual.Count131072.C047713.packed 64 cuts47713 = true := by
 decide +kernel
def pointBounds47713 : List (Nat × Nat × Nat) := [(6257803264,111073685610288,111074072399365)]
theorem point_links_checked47713 : (cuts47713.take 1).map (fun c => (6257770497-1+2*2^10*c.k,111073619264875+c.lower,111074006053913+c.upper)) = pointBounds47713 := by
 decide +kernel
def cuts47714 : List PrefixCut := [⟨48,196197395,196197508⟩,
⟨64,260651288,260651443⟩]
theorem checked47714 : checkPrefixCuts (2^48) 6257901569 10 Manual.Count131072.C047714.packed 64 cuts47714 = true := by
 decide +kernel
def pointBounds47714 : List (Nat × Nat × Nat) := [(6257999872,111074075984065,111074462773364)]
theorem point_links_checked47714 : (cuts47714.take 1).map (fun c => (6257901569-1+2*2^10*c.k,111073879786670+c.lower,111074266575856+c.upper)) = pointBounds47714 := by
 decide +kernel
def cuts47715 : List PrefixCut := [⟨64,264423950,264424100⟩]
theorem checked47715 : checkPrefixCuts (2^48) 6258032641 10 Manual.Count131072.C047715.packed 64 cuts47715 = true := by
 decide +kernel
def cuts47716 : List PrefixCut := [⟨16,65351750,65351785⟩,
⟨64,259515919,259516067⟩]
theorem checked47716 : checkPrefixCuts (2^48) 6258163713 10 Manual.Count131072.C047716.packed 64 cuts47716 = true := by
 decide +kernel
def pointBounds47716 : List (Nat × Nat × Nat) := [(6258196480,111074470213658,111074857003184)]
theorem point_links_checked47716 : (cuts47716.take 1).map (fun c => (6258163713-1+2*2^10*c.k,111074404861908+c.lower,111074791651399+c.upper)) = pointBounds47716 := by
 decide +kernel
def cuts47717 : List PrefixCut := [⟨48,194565902,194566011⟩,
⟨64,259870279,259870430⟩]
theorem checked47717 : checkPrefixCuts (2^48) 6258294785 10 Manual.Count131072.C047717.packed 64 cuts47717 = true := by
 decide +kernel
def pointBounds47717 : List (Nat × Nat × Nat) := [(6258393088,111074858943729,111075245733477)]
theorem point_links_checked47717 : (cuts47717.take 1).map (fun c => (6258294785-1+2*2^10*c.k,111074664377827+c.lower,111075051167466+c.upper)) = pointBounds47717 := by
 decide +kernel
def cuts47718 : List PrefixCut := [⟨64,263687727,263687876⟩]
theorem checked47718 : checkPrefixCuts (2^48) 6258425857 10 Manual.Count131072.C047718.packed 64 cuts47718 = true := by
 decide +kernel
def cuts47719 : List PrefixCut := [⟨16,64897901,64897940⟩,
⟨64,261793291,261793442⟩]
theorem checked47719 : checkPrefixCuts (2^48) 6258556929 10 Manual.Count131072.C047719.packed 64 cuts47719 = true := by
 decide +kernel
def pointBounds47719 : List (Nat × Nat × Nat) := [(6258589696,111075252833734,111075639623712)]
theorem point_links_checked47719 : (cuts47719.take 1).map (fun c => (6258556929-1+2*2^10*c.k,111075187935833+c.lower,111075574725772+c.upper)) = pointBounds47719 := by
 decide +kernel
def cuts47720 : List PrefixCut := [⟨48,196622448,196622561⟩,
⟨64,260573549,260573696⟩]
theorem checked47720 : checkPrefixCuts (2^48) 6258688001 10 Manual.Count131072.C047720.packed 64 cuts47720 = true := by
 decide +kernel
def pointBounds47720 : List (Nat × Nat × Nat) := [(6258786304,111075646351572,111076033141775)]
theorem point_links_checked47720 : (cuts47720.take 1).map (fun c => (6258688001-1+2*2^10*c.k,111075449729124+c.lower,111075836519214+c.upper)) = pointBounds47720 := by
 decide +kernel
def cuts47721 : List PrefixCut := [⟨64,260163321,260163471⟩]
theorem checked47721 : checkPrefixCuts (2^48) 6258819073 10 Manual.Count131072.C047721.packed 64 cuts47721 = true := by
 decide +kernel
def cuts47722 : List PrefixCut := [⟨16,63544680,63544718⟩,
⟨64,259708161,259708310⟩]
theorem checked47722 : checkPrefixCuts (2^48) 6258950145 10 Manual.Count131072.C047722.packed 64 cuts47722 = true := by
 decide +kernel
def pointBounds47722 : List (Nat × Nat × Nat) := [(6258982912,111076034010674,111076420801099)]
theorem point_links_checked47722 : (cuts47722.take 1).map (fun c => (6258950145-1+2*2^10*c.k,111075970465994+c.lower,111076357256381+c.upper)) = pointBounds47722 := by
 decide +kernel
def cuts47723 : List PrefixCut := [⟨48,196700053,196700163⟩,
⟨64,261636469,261636614⟩]
theorem checked47723 : checkPrefixCuts (2^48) 6259081217 10 Manual.Count131072.C047723.packed 64 cuts47723 = true := by
 decide +kernel
def pointBounds47723 : List (Nat × Nat × Nat) := [(6259179520,111076426874208,111076813664854)]
theorem point_links_checked47723 : (cuts47723.take 1).map (fun c => (6259081217-1+2*2^10*c.k,111076230174155+c.lower,111076616964691+c.upper)) = pointBounds47723 := by
 decide +kernel
def cuts47724 : List PrefixCut := [⟨64,260596665,260596816⟩]
theorem checked47724 : checkPrefixCuts (2^48) 6259212289 10 Manual.Count131072.C047724.packed 64 cuts47724 = true := by
 decide +kernel
def cuts47725 : List PrefixCut := [⟨16,65474340,65474377⟩,
⟨64,261130841,261130988⟩]
theorem checked47725 : checkPrefixCuts (2^48) 6259343361 10 Manual.Count131072.C047725.packed 64 cuts47725 = true := by
 decide +kernel
def pointBounds47725 : List (Nat × Nat × Nat) := [(6259376128,111076817881629,111077204672498)]
theorem point_links_checked47725 : (cuts47725.take 1).map (fun c => (6259343361-1+2*2^10*c.k,111076752407289+c.lower,111077139198121+c.upper)) = pointBounds47725 := by
 decide +kernel
def cuts47726 : List PrefixCut := [⟨48,198846132,198846242⟩,
⟨64,263418732,263418876⟩]
theorem checked47726 : checkPrefixCuts (2^48) 6259474433 10 Manual.Count131072.C047726.packed 64 cuts47726 = true := by
 decide +kernel
def pointBounds47726 : List (Nat × Nat × Nat) := [(6259572736,111077212384262,111077599175351)]
theorem point_links_checked47726 : (cuts47726.take 1).map (fun c => (6259474433-1+2*2^10*c.k,111077013538130+c.lower,111077400329109+c.upper)) = pointBounds47726 := by
 decide +kernel
def cuts47727 : List PrefixCut := [⟨64,260265546,260265701⟩]
theorem checked47727 : checkPrefixCuts (2^48) 6259605505 10 Manual.Count131072.C047727.packed 64 cuts47727 = true := by
 decide +kernel
def cuts47728 : List PrefixCut := [⟨16,64615877,64615911⟩,
⟨64,261564086,261564226⟩]
theorem checked47728 : checkPrefixCuts (2^48) 6259736577 10 Manual.Count131072.C047728.packed 64 cuts47728 = true := by
 decide +kernel
def pointBounds47728 : List (Nat × Nat × Nat) := [(6259769344,111077601838285,111077988629597)]
theorem point_links_checked47728 : (cuts47728.take 1).map (fun c => (6259736577-1+2*2^10*c.k,111077537222408+c.lower,111077924013686+c.upper)) = pointBounds47728 := by
 decide +kernel
def cuts47729 : List PrefixCut := [⟨48,196180731,196180843⟩,
⟨64,260839203,260839349⟩]
theorem checked47729 : checkPrefixCuts (2^48) 6259867649 10 Manual.Count131072.C047729.packed 64 cuts47729 = true := by
 decide +kernel
def pointBounds47729 : List (Nat × Nat × Nat) := [(6259965952,111077994967225,111078381758755)]
theorem point_links_checked47729 : (cuts47729.take 1).map (fun c => (6259867649-1+2*2^10*c.k,111077798786494+c.lower,111078185577912+c.upper)) = pointBounds47729 := by
 decide +kernel
def cuts47730 : List PrefixCut := [⟨64,256472263,256472414⟩]
theorem checked47730 : checkPrefixCuts (2^48) 6259998721 10 Manual.Count131072.C047730.packed 64 cuts47730 = true := by
 decide +kernel
def cuts47731 : List PrefixCut := [⟨16,64386999,64387038⟩,
⟨64,262312015,262312167⟩]
theorem checked47731 : checkPrefixCuts (2^48) 6260129793 10 Manual.Count131072.C047731.packed 64 cuts47731 = true := by
 decide +kernel
def pointBounds47731 : List (Nat × Nat × Nat) := [(6260162560,111078380484959,111078767276713)]
theorem point_links_checked47731 : (cuts47731.take 1).map (fun c => (6260129793-1+2*2^10*c.k,111078316097960+c.lower,111078702889675+c.upper)) = pointBounds47731 := by
 decide +kernel
def cuts47732 : List PrefixCut := [⟨48,196303268,196303386⟩,
⟨64,263340632,263340788⟩]
theorem checked47732 : checkPrefixCuts (2^48) 6260260865 10 Manual.Count131072.C047732.packed 64 cuts47732 = true := by
 decide +kernel
def pointBounds47732 : List (Nat × Nat × Nat) := [(6260359168,111078774713243,111079161505228)]
theorem point_links_checked47732 : (cuts47732.take 1).map (fun c => (6260260865-1+2*2^10*c.k,111078578409975+c.lower,111078965201842+c.upper)) = pointBounds47732 := by
 decide +kernel
def cuts47733 : List PrefixCut := [⟨64,259423569,259423720⟩]
theorem checked47733 : checkPrefixCuts (2^48) 6260391937 10 Manual.Count131072.C047733.packed 64 cuts47733 = true := by
 decide +kernel
def cuts47734 : List PrefixCut := [⟨16,65776725,65776762⟩,
⟨64,260047584,260047731⟩]
theorem checked47734 : checkPrefixCuts (2^48) 6260523009 10 Manual.Count131072.C047734.packed 64 cuts47734 = true := by
 decide +kernel
def pointBounds47734 : List (Nat × Nat × Nat) := [(6260555776,111079166950901,111079553743112)]
theorem point_links_checked47734 : (cuts47734.take 1).map (fun c => (6260523009-1+2*2^10*c.k,111079101174176+c.lower,111079487966350+c.upper)) = pointBounds47734 := by
 decide +kernel
def cuts47735 : List PrefixCut := [⟨48,194942174,194942287⟩,
⟨64,262155162,262155313⟩]
theorem checked47735 : checkPrefixCuts (2^48) 6260654081 10 Manual.Count131072.C047735.packed 64 cuts47735 = true := by
 decide +kernel
def pointBounds47735 : List (Nat × Nat × Nat) := [(6260752384,111079556163934,111079942956368)]
theorem point_links_checked47735 : (cuts47735.take 1).map (fun c => (6260654081-1+2*2^10*c.k,111079361221760+c.lower,111079748014081+c.upper)) = pointBounds47735 := by
 decide +kernel
def cuts47736 : List PrefixCut := [⟨64,262958930,262959081⟩]
theorem checked47736 : checkPrefixCuts (2^48) 6260785153 10 Manual.Count131072.C047736.packed 64 cuts47736 = true := by
 decide +kernel
def cuts47737 : List PrefixCut := [⟨16,64333960,64333994⟩,
⟨64,257783373,257783513⟩]
theorem checked47737 : checkPrefixCuts (2^48) 6260916225 10 Manual.Count131072.C047737.packed 64 cuts47737 = true := by
 decide +kernel
def pointBounds47737 : List (Nat × Nat × Nat) := [(6260948992,111079950669812,111080337462469)]
theorem point_links_checked47737 : (cuts47737.take 1).map (fun c => (6260916225-1+2*2^10*c.k,111079886335852+c.lower,111080273128475+c.upper)) = pointBounds47737 := by
 decide +kernel
def cuts47738 : List PrefixCut := [⟨48,196008897,196009014⟩,
⟨64,261509345,261509498⟩]
theorem checked47738 : checkPrefixCuts (2^48) 6261047297 10 Manual.Count131072.C047738.packed 64 cuts47738 = true := by
 decide +kernel
def pointBounds47738 : List (Nat × Nat × Nat) := [(6261145600,111080340128122,111080726921002)]
theorem point_links_checked47738 : (cuts47738.take 1).map (fun c => (6261047297-1+2*2^10*c.k,111080144119225+c.lower,111080530911988+c.upper)) = pointBounds47738 := by
 decide +kernel
def cuts47739 : List PrefixCut := [⟨64,263257135,263257289⟩]
theorem checked47739 : checkPrefixCuts (2^48) 6261178369 10 Manual.Count131072.C047739.packed 64 cuts47739 = true := by
 decide +kernel
def cuts47740 : List PrefixCut := [⟨16,65004236,65004273⟩,
⟨64,262891959,262892110⟩]
theorem checked47740 : checkPrefixCuts (2^48) 6261309441 10 Manual.Count131072.C047740.packed 64 cuts47740 = true := by
 decide +kernel
def pointBounds47740 : List (Nat × Nat × Nat) := [(6261342208,111080733889941,111081120683048)]
theorem point_links_checked47740 : (cuts47740.take 1).map (fun c => (6261309441-1+2*2^10*c.k,111080668885705+c.lower,111081055678775+c.upper)) = pointBounds47740 := by
 decide +kernel
def cuts47741 : List PrefixCut := [⟨48,197704785,197704904⟩,
⟨64,262122253,262122411⟩]
theorem checked47741 : checkPrefixCuts (2^48) 6261440513 10 Manual.Count131072.C047741.packed 64 cuts47741 = true := by
 decide +kernel
def pointBounds47741 : List (Nat × Nat × Nat) := [(6261538816,111081129482449,111081516275789)]
theorem point_links_checked47741 : (cuts47741.take 1).map (fun c => (6261440513-1+2*2^10*c.k,111080931777664+c.lower,111081318570885+c.upper)) = pointBounds47741 := by
 decide +kernel
def cuts47742 : List PrefixCut := [⟨64,261082892,261083043⟩]
theorem checked47742 : checkPrefixCuts (2^48) 6261571585 10 Manual.Count131072.C047742.packed 64 cuts47742 = true := by
 decide +kernel
def cuts47743 : List PrefixCut := [⟨16,65764332,65764369⟩,
⟨64,266831175,266831325⟩]
theorem checked47743 : checkPrefixCuts (2^48) 6261702657 10 Manual.Count131072.C047743.packed 64 cuts47743 = true := by
 decide +kernel
def pointBounds47743 : List (Nat × Nat × Nat) := [(6261735424,111081520747141,111081907540708)]
theorem point_links_checked47743 : (cuts47743.take 1).map (fun c => (6261702657-1+2*2^10*c.k,111081454982809+c.lower,111081841776339+c.upper)) = pointBounds47743 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S5.B000241
