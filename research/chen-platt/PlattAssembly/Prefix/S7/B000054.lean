import PlattAssemblyKernel
import PlattCertificates.Count131072.C061728
import PlattCertificates.Count131072.C061729
import PlattCertificates.Count131072.C061730
import PlattCertificates.Count131072.C061731
import PlattCertificates.Count131072.C061732
import PlattCertificates.Count131072.C061733
import PlattCertificates.Count131072.C061734
import PlattCertificates.Count131072.C061735
import PlattCertificates.Count131072.C061736
import PlattCertificates.Count131072.C061737
import PlattCertificates.Count131072.C061738
import PlattCertificates.Count131072.C061739
import PlattCertificates.Count131072.C061740
import PlattCertificates.Count131072.C061741
import PlattCertificates.Count131072.C061742
import PlattCertificates.Count131072.C061743
import PlattCertificates.Count131072.C061744
import PlattCertificates.Count131072.C061745
import PlattCertificates.Count131072.C061746
import PlattCertificates.Count131072.C061747
import PlattCertificates.Count131072.C061748
import PlattCertificates.Count131072.C061749
import PlattCertificates.Count131072.C061750
import PlattCertificates.Count131072.C061751
import PlattCertificates.Count131072.C061752
import PlattCertificates.Count131072.C061753
import PlattCertificates.Count131072.C061754
import PlattCertificates.Count131072.C061755
import PlattCertificates.Count131072.C061756
import PlattCertificates.Count131072.C061757
import PlattCertificates.Count131072.C061758
import PlattCertificates.Count131072.C061759
namespace ChenEffective.PlattWindow.Assembly.Prefix.S7.B000054
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts61728 : List PrefixCut := [⟨28,88356736,88356783⟩,
⟨64,201400976,201401085⟩]
theorem checked61728 : checkPrefixCuts (2^48) 8094744577 10 Manual.Count131072.C061728.packed 64 cuts61728 = true := by
 decide +kernel
def pointBounds61728 : List (Nat × Nat × Nat) := [(8094801920,114267278156648,114267666764440)]
theorem point_links_checked61728 : (cuts61728.take 1).map (fun c => (8094744577-1+2*2^10*c.k,114267189799912+c.lower,114267578407657+c.upper)) = pointBounds61728 := by
 decide +kernel
def cuts61729 : List PrefixCut := [⟨64,199068014,199068126⟩]
theorem checked61729 : checkPrefixCuts (2^48) 8094875649 10 Manual.Count131072.C061729.packed 64 cuts61729 = true := by
 decide +kernel
def cuts61730 : List PrefixCut := [⟨24,75871011,75871056⟩,
⟨64,201185827,201185938⟩]
theorem checked61730 : checkPrefixCuts (2^48) 8095006721 10 Manual.Count131072.C061730.packed 64 cuts61730 = true := by
 decide +kernel
def pointBounds61730 : List (Nat × Nat × Nat) := [(8095055872,114267666139913,114268054747924)]
theorem point_links_checked61730 : (cuts61730.take 1).map (fun c => (8095006721-1+2*2^10*c.k,114267590268902+c.lower,114267978876868+c.upper)) = pointBounds61730 := by
 decide +kernel
def cuts61731 : List PrefixCut := [⟨64,198852934,198853053⟩]
theorem checked61731 : checkPrefixCuts (2^48) 8095137793 10 Manual.Count131072.C061731.packed 64 cuts61731 = true := by
 decide +kernel
def cuts61732 : List PrefixCut := [⟨20,60674014,60674048⟩,
⟨64,197667529,197667644⟩]
theorem checked61732 : checkPrefixCuts (2^48) 8095268865 10 Manual.Count131072.C061732.packed 64 cuts61732 = true := by
 decide +kernel
def pointBounds61732 : List (Nat × Nat × Nat) := [(8095309824,114268050981677,114268439589907)]
theorem point_links_checked61732 : (cuts61732.take 1).map (fun c => (8095268865-1+2*2^10*c.k,114267990307663+c.lower,114268378915859+c.upper)) = pointBounds61732 := by
 decide +kernel
def cuts61733 : List PrefixCut := [⟨64,199750506,199750614⟩]
theorem checked61733 : checkPrefixCuts (2^48) 8095399937 10 Manual.Count131072.C061733.packed 64 cuts61733 = true := by
 decide +kernel
def cuts61734 : List PrefixCut := [⟨16,50206580,50206611⟩,
⟨64,197417755,197417873⟩]
theorem checked61734 : checkPrefixCuts (2^48) 8095531009 10 Manual.Count131072.C061734.packed 64 cuts61734 = true := by
 decide +kernel
def pointBounds61734 : List (Nat × Nat × Nat) := [(8095563776,114268437932278,114268826540728)]
theorem point_links_checked61734 : (cuts61734.take 1).map (fun c => (8095531009-1+2*2^10*c.k,114268387725698+c.lower,114268776334117+c.upper)) = pointBounds61734 := by
 decide +kernel
def cuts61735 : List PrefixCut := [⟨64,198214218,198214331⟩]
theorem checked61735 : checkPrefixCuts (2^48) 8095662081 10 Manual.Count131072.C061735.packed 64 cuts61735 = true := by
 decide +kernel
def cuts61736 : List PrefixCut := [⟨12,36575926,36575948⟩,
⟨64,199010671,199010780⟩]
theorem checked61736 : checkPrefixCuts (2^48) 8095793153 10 Manual.Count131072.C061736.packed 64 cuts61736 = true := by
 decide +kernel
def pointBounds61736 : List (Nat × Nat × Nat) := [(8095817728,114268819933597,114269208542269)]
theorem point_links_checked61736 : (cuts61736.take 1).map (fun c => (8095793153-1+2*2^10*c.k,114268783357671+c.lower,114269171966321+c.upper)) = pointBounds61736 := by
 decide +kernel
def cuts61737 : List PrefixCut := [⟨64,200120012,200120125⟩]
theorem checked61737 : checkPrefixCuts (2^48) 8095924225 10 Manual.Count131072.C061737.packed 64 cuts61737 = true := by
 decide +kernel
def cuts61738 : List PrefixCut := [⟨8,25171222,25171236⟩,
⟨64,201611724,201611844⟩]
theorem checked61738 : checkPrefixCuts (2^48) 8096055297 10 Manual.Count131072.C061738.packed 64 cuts61738 = true := by
 decide +kernel
def pointBounds61738 : List (Nat × Nat × Nat) := [(8096071680,114269207659576,114269596268462)]
theorem point_links_checked61738 : (cuts61738.take 1).map (fun c => (8096055297-1+2*2^10*c.k,114269182488354+c.lower,114269571097226+c.upper)) = pointBounds61738 := by
 decide +kernel
def cuts61739 : List PrefixCut := [⟨64,198653332,198653443⟩]
theorem checked61739 : checkPrefixCuts (2^48) 8096186369 10 Manual.Count131072.C061739.packed 64 cuts61739 = true := by
 decide +kernel
def cuts61740 : List PrefixCut := [⟨4,11055516,11055523⟩,
⟨64,195903650,195903759⟩]
theorem checked61740 : checkPrefixCuts (2^48) 8096317441 10 Manual.Count131072.C061740.packed 64 cuts61740 = true := by
 decide +kernel
def pointBounds61740 : List (Nat × Nat × Nat) := [(8096325632,114269593808926,114269982418036)]
theorem point_links_checked61740 : (cuts61740.take 1).map (fun c => (8096317441-1+2*2^10*c.k,114269582753410+c.lower,114269971362513+c.upper)) = pointBounds61740 := by
 decide +kernel
def cuts61741 : List PrefixCut := [⟨64,201393360,201393475⟩]
theorem checked61741 : checkPrefixCuts (2^48) 8096448513 10 Manual.Count131072.C061741.packed 64 cuts61741 = true := by
 decide +kernel
def pointBounds61741 : List (Nat × Nat × Nat) := [(8096579584,114269980050420,114270368659747)]
theorem point_links_checked61741 : (cuts61741.take 1).map (fun c => (8096448513-1+2*2^10*c.k,114269778657060+c.lower,114270167266272+c.upper)) = pointBounds61741 := by
 decide +kernel
def cuts61742 : List PrefixCut := [⟨64,202224427,202224545⟩]
theorem checked61742 : checkPrefixCuts (2^48) 8096579585 10 Manual.Count131072.C061742.packed 64 cuts61742 = true := by
 decide +kernel
def cuts61743 : List PrefixCut := [⟨60,188211434,188211536⟩,
⟨64,200274389,200274499⟩]
theorem checked61743 : checkPrefixCuts (2^48) 8096710657 10 Manual.Count131072.C061743.packed 64 cuts61743 = true := by
 decide +kernel
def pointBounds61743 : List (Nat × Nat × Nat) := [(8096833536,114270370486281,114270759095828)]
theorem point_links_checked61743 : (cuts61743.take 1).map (fun c => (8096710657-1+2*2^10*c.k,114270182274847+c.lower,114270570884292+c.upper)) = pointBounds61743 := by
 decide +kernel
def cuts61744 : List PrefixCut := [⟨64,201314052,201314166⟩]
theorem checked61744 : checkPrefixCuts (2^48) 8096841729 10 Manual.Count131072.C061744.packed 64 cuts61744 = true := by
 decide +kernel
def cuts61745 : List PrefixCut := [⟨56,175412749,175412852⟩,
⟨64,199746464,199746582⟩]
theorem checked61745 : checkPrefixCuts (2^48) 8096972801 10 Manual.Count131072.C061745.packed 64 cuts61745 = true := by
 decide +kernel
def pointBounds61745 : List (Nat × Nat × Nat) := [(8097087488,114270759276037,114271147885809)]
theorem point_links_checked61745 : (cuts61745.take 1).map (fun c => (8096972801-1+2*2^10*c.k,114270583863288+c.lower,114270972472957+c.upper)) = pointBounds61745 := by
 decide +kernel
def cuts61746 : List PrefixCut := [⟨64,197657502,197657614⟩]
theorem checked61746 : checkPrefixCuts (2^48) 8097103873 10 Manual.Count131072.C061746.packed 64 cuts61746 = true := by
 decide +kernel
def cuts61747 : List PrefixCut := [⟨52,161606799,161606887⟩,
⟨64,198801436,198801547⟩]
theorem checked61747 : checkPrefixCuts (2^48) 8097234945 10 Manual.Count131072.C061747.packed 64 cuts61747 = true := by
 decide +kernel
def pointBounds61747 : List (Nat × Nat × Nat) := [(8097341440,114271142874053,114271531484040)]
theorem point_links_checked61747 : (cuts61747.take 1).map (fun c => (8097234945-1+2*2^10*c.k,114270981267254+c.lower,114271369877153+c.upper)) = pointBounds61747 := by
 decide +kernel
def cuts61748 : List PrefixCut := [⟨64,198450599,198450708⟩]
theorem checked61748 : checkPrefixCuts (2^48) 8097366017 10 Manual.Count131072.C061748.packed 64 cuts61748 = true := by
 decide +kernel
def cuts61749 : List PrefixCut := [⟨48,149331194,149331280⟩,
⟨64,199942096,199942213⟩]
theorem checked61749 : checkPrefixCuts (2^48) 8097497089 10 Manual.Count131072.C061749.packed 64 cuts61749 = true := by
 decide +kernel
def pointBounds61749 : List (Nat × Nat × Nat) := [(8097595392,114271527850483,114271916460688)]
theorem point_links_checked61749 : (cuts61749.take 1).map (fun c => (8097497089-1+2*2^10*c.k,114271378519289+c.lower,114271767129408+c.upper)) = pointBounds61749 := by
 decide +kernel
def cuts61750 : List PrefixCut := [⟨64,198896059,198896173⟩]
theorem checked61750 : checkPrefixCuts (2^48) 8097628161 10 Manual.Count131072.C061750.packed 64 cuts61750 = true := by
 decide +kernel
def cuts61751 : List PrefixCut := [⟨44,139489518,139489599⟩,
⟨64,201638841,201638960⟩]
theorem checked61751 : checkPrefixCuts (2^48) 8097759233 10 Manual.Count131072.C061751.packed 64 cuts61751 = true := by
 decide +kernel
def pointBounds61751 : List (Nat × Nat × Nat) := [(8097849344,114271916846962,114272305457393)]
theorem point_links_checked61751 : (cuts61751.take 1).map (fun c => (8097759233-1+2*2^10*c.k,114271777357444+c.lower,114272165967794+c.upper)) = pointBounds61751 := by
 decide +kernel
def cuts61752 : List PrefixCut := [⟨64,198785359,198785472⟩]
theorem checked61752 : checkPrefixCuts (2^48) 8097890305 10 Manual.Count131072.C061752.packed 64 cuts61752 = true := by
 decide +kernel
def cuts61753 : List PrefixCut := [⟨40,125616503,125616575⟩,
⟨64,200485279,200485394⟩]
theorem checked61753 : checkPrefixCuts (2^48) 8098021377 10 Manual.Count131072.C061753.packed 64 cuts61753 = true := by
 decide +kernel
def pointBounds61753 : List (Nat × Nat × Nat) := [(8098103296,114272303398147,114272692008801)]
theorem point_links_checked61753 : (cuts61753.take 1).map (fun c => (8098021377-1+2*2^10*c.k,114272177781644+c.lower,114272566392226+c.upper)) = pointBounds61753 := by
 decide +kernel
def cuts61754 : List PrefixCut := [⟨64,202115645,202115763⟩]
theorem checked61754 : checkPrefixCuts (2^48) 8098152449 10 Manual.Count131072.C061754.packed 64 cuts61754 = true := by
 decide +kernel
def cuts61755 : List PrefixCut := [⟨36,111049230,111049294⟩,
⟨64,195925615,195925728⟩]
theorem checked61755 : checkPrefixCuts (2^48) 8098283521 10 Manual.Count131072.C061755.packed 64 cuts61755 = true := by
 decide +kernel
def pointBounds61755 : List (Nat × Nat × Nat) := [(8098357248,114272691431798,114273080042677)]
theorem point_links_checked61755 : (cuts61755.take 1).map (fun c => (8098283521-1+2*2^10*c.k,114272580382568+c.lower,114272968993383+c.upper)) = pointBounds61755 := by
 decide +kernel
def cuts61756 : List PrefixCut := [⟨64,200614574,200614691⟩]
theorem checked61756 : checkPrefixCuts (2^48) 8098414593 10 Manual.Count131072.C061756.packed 64 cuts61756 = true := by
 decide +kernel
def cuts61757 : List PrefixCut := [⟨32,101557292,101557352⟩,
⟨64,200090004,200090123⟩]
theorem checked61757 : checkPrefixCuts (2^48) 8098545665 10 Manual.Count131072.C061757.packed 64 cuts61757 = true := by
 decide +kernel
def pointBounds61757 : List (Nat × Nat × Nat) := [(8098611200,114273078480049,114273467091154)]
theorem point_links_checked61757 : (cuts61757.take 1).map (fun c => (8098545665-1+2*2^10*c.k,114272976922757+c.lower,114273365533802+c.upper)) = pointBounds61757 := by
 decide +kernel
def cuts61758 : List PrefixCut := [⟨64,198070946,198071057⟩]
theorem checked61758 : checkPrefixCuts (2^48) 8098676737 10 Manual.Count131072.C061758.packed 64 cuts61758 = true := by
 decide +kernel
def cuts61759 : List PrefixCut := [⟨28,87165491,87165540⟩,
⟨64,200361542,200361656⟩]
theorem checked61759 : checkPrefixCuts (2^48) 8098807809 10 Manual.Count131072.C061759.packed 64 cuts61759 = true := by
 decide +kernel
def pointBounds61759 : List (Nat × Nat × Nat) := [(8098865152,114273462249198,114273850860522)]
theorem point_links_checked61759 : (cuts61759.take 1).map (fun c => (8098807809-1+2*2^10*c.k,114273375083707+c.lower,114273763694982+c.upper)) = pointBounds61759 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S7.B000054
