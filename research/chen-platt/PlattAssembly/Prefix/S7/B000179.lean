import PlattAssemblyKernel
import PlattCertificates.Count131072.C065728
import PlattCertificates.Count131072.C065729
import PlattCertificates.Count131072.C065730
import PlattCertificates.Count131072.C065731
import PlattCertificates.Count131072.C065732
import PlattCertificates.Count131072.C065733
import PlattCertificates.Count131072.C065734
import PlattCertificates.Count131072.C065735
import PlattCertificates.Count131072.C065736
import PlattCertificates.Count131072.C065737
import PlattCertificates.Count131072.C065738
import PlattCertificates.Count131072.C065739
import PlattCertificates.Count131072.C065740
import PlattCertificates.Count131072.C065741
import PlattCertificates.Count131072.C065742
import PlattCertificates.Count131072.C065743
import PlattCertificates.Count131072.C065744
import PlattCertificates.Count131072.C065745
import PlattCertificates.Count131072.C065746
import PlattCertificates.Count131072.C065747
import PlattCertificates.Count131072.C065748
import PlattCertificates.Count131072.C065749
import PlattCertificates.Count131072.C065750
import PlattCertificates.Count131072.C065751
import PlattCertificates.Count131072.C065752
import PlattCertificates.Count131072.C065753
import PlattCertificates.Count131072.C065754
import PlattCertificates.Count131072.C065755
import PlattCertificates.Count131072.C065756
import PlattCertificates.Count131072.C065757
import PlattCertificates.Count131072.C065758
import PlattCertificates.Count131072.C065759
namespace ChenEffective.PlattWindow.Assembly.Prefix.S7.B000179
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts65728 : List PrefixCut := [⟨64,185394458,185394576⟩]
theorem checked65728 : checkPrefixCuts (2^48) 8619032577 10 Manual.Count131072.C065728.packed 64 cuts65728 = true := by
 decide +kernel
def cuts65729 : List PrefixCut := [⟨39,115572122,115572191⟩,
⟨64,189147149,189147255⟩]
theorem checked65729 : checkPrefixCuts (2^48) 8619163649 10 Manual.Count131072.C065729.packed 64 cuts65729 = true := by
 decide +kernel
def pointBounds65729 : List (Nat × Nat × Nat) := [(8619243520,115040725991040,115041115044725)]
theorem point_links_checked65729 : (cuts65729.take 1).map (fun c => (8619163649-1+2*2^10*c.k,115040610418918+c.lower,115040999472534+c.upper)) = pointBounds65729 := by
 decide +kernel
def cuts65730 : List PrefixCut := [⟨64,186270547,186270653⟩]
theorem checked65730 : checkPrefixCuts (2^48) 8619294721 10 Manual.Count131072.C065730.packed 64 cuts65730 = true := by
 decide +kernel
def cuts65731 : List PrefixCut := [⟨43,123797785,123797861⟩,
⟨64,186071746,186071860⟩]
theorem checked65731 : checkPrefixCuts (2^48) 8619425793 10 Manual.Count131072.C065731.packed 64 cuts65731 = true := by
 decide +kernel
def pointBounds65731 : List (Nat × Nat × Nat) := [(8619513856,115041109634399,115041498688303)]
theorem point_links_checked65731 : (cuts65731.take 1).map (fun c => (8619425793-1+2*2^10*c.k,115040985836614+c.lower,115041374890442+c.upper)) = pointBounds65731 := by
 decide +kernel
def cuts65732 : List PrefixCut := [⟨64,188550726,188550837⟩]
theorem checked65732 : checkPrefixCuts (2^48) 8619556865 10 Manual.Count131072.C065732.packed 64 cuts65732 = true := by
 decide +kernel
def cuts65733 : List PrefixCut := [⟨47,136235416,136235494⟩,
⟨64,185608947,185609056⟩]
theorem checked65733 : checkPrefixCuts (2^48) 8619687937 10 Manual.Count131072.C065733.packed 64 cuts65733 = true := by
 decide +kernel
def pointBounds65733 : List (Nat × Nat × Nat) := [(8619784192,115041496694502,115041885748633)]
theorem point_links_checked65733 : (cuts65733.take 1).map (fun c => (8619687937-1+2*2^10*c.k,115041360459086+c.lower,115041749513139+c.upper)) = pointBounds65733 := by
 decide +kernel
def cuts65734 : List PrefixCut := [⟨64,190373614,190373723⟩]
theorem checked65734 : checkPrefixCuts (2^48) 8619819009 10 Manual.Count131072.C065734.packed 64 cuts65734 = true := by
 decide +kernel
def cuts65735 : List PrefixCut := [⟨51,149782484,149782573⟩,
⟨64,188836001,188836113⟩]
theorem checked65735 : checkPrefixCuts (2^48) 8619950081 10 Manual.Count131072.C065735.packed 64 cuts65735 = true := by
 decide +kernel
def pointBounds65735 : List (Nat × Nat × Nat) := [(8620054528,115041886224131,115042275278491)]
theorem point_links_checked65735 : (cuts65735.take 1).map (fun c => (8619950081-1+2*2^10*c.k,115041736441647+c.lower,115042125495918+c.upper)) = pointBounds65735 := by
 decide +kernel
def cuts65736 : List PrefixCut := [⟨64,187820884,187820991⟩]
theorem checked65736 : checkPrefixCuts (2^48) 8620081153 10 Manual.Count131072.C065736.packed 64 cuts65736 = true := by
 decide +kernel
def cuts65737 : List PrefixCut := [⟨55,161369560,161369654⟩,
⟨64,188307817,188307927⟩]
theorem checked65737 : checkPrefixCuts (2^48) 8620212225 10 Manual.Count131072.C065737.packed 64 cuts65737 = true := by
 decide +kernel
def pointBounds65737 : List (Nat × Nat × Nat) := [(8620324864,115042274468092,115042663522676)]
theorem point_links_checked65737 : (cuts65737.take 1).map (fun c => (8620212225-1+2*2^10*c.k,115042113098532+c.lower,115042502153022+c.upper)) = pointBounds65737 := by
 decide +kernel
def cuts65738 : List PrefixCut := [⟨64,184909143,184909258⟩]
theorem checked65738 : checkPrefixCuts (2^48) 8620343297 10 Manual.Count131072.C065738.packed 64 cuts65738 = true := by
 decide +kernel
def cuts65739 : List PrefixCut := [⟨59,172955921,172956016⟩,
⟨64,188759212,188759314⟩]
theorem checked65739 : checkPrefixCuts (2^48) 8620474369 10 Manual.Count131072.C065739.packed 64 cuts65739 = true := by
 decide +kernel
def pointBounds65739 : List (Nat × Nat × Nat) := [(8620595200,115042659271413,115043048326223)]
theorem point_links_checked65739 : (cuts65739.take 1).map (fun c => (8620474369-1+2*2^10*c.k,115042486315492+c.lower,115042875370207+c.upper)) = pointBounds65739 := by
 decide +kernel
def cuts65740 : List PrefixCut := [⟨64,187123783,187123889⟩]
theorem checked65740 : checkPrefixCuts (2^48) 8620605441 10 Manual.Count131072.C065740.packed 64 cuts65740 = true := by
 decide +kernel
def cuts65741 : List PrefixCut := [⟨63,186402662,186402767⟩,
⟨64,189700354,189700461⟩]
theorem checked65741 : checkPrefixCuts (2^48) 8620736513 10 Manual.Count131072.C065741.packed 64 cuts65741 = true := by
 decide +kernel
def pointBounds65741 : List (Nat × Nat × Nat) := [(8620865536,115043048601149,115043437656177)]
theorem point_links_checked65741 : (cuts65741.take 1).map (fun c => (8620736513-1+2*2^10*c.k,115042862198487+c.lower,115043251253410+c.upper)) = pointBounds65741 := by
 decide +kernel
def cuts65742 : List PrefixCut := [⟨64,188685302,188685412⟩]
theorem checked65742 : checkPrefixCuts (2^48) 8620867585 10 Manual.Count131072.C065742.packed 64 cuts65742 = true := by
 decide +kernel
def cuts65743 : List PrefixCut := [⟨64,184927726,184927827⟩]
theorem checked65743 : checkPrefixCuts (2^48) 8620998657 10 Manual.Count131072.C065743.packed 64 cuts65743 = true := by
 decide +kernel
def cuts65744 : List PrefixCut := [⟨3,8292950,8292955⟩,
⟨64,184206631,184206744⟩]
theorem checked65744 : checkPrefixCuts (2^48) 8621129729 10 Manual.Count131072.C065744.packed 64 cuts65744 = true := by
 decide +kernel
def pointBounds65744 : List (Nat × Nat × Nat) := [(8621135872,115043433804819,115043822860065)]
theorem point_links_checked65744 : (cuts65744.take 1).map (fun c => (8621129729-1+2*2^10*c.k,115043425511869+c.lower,115043814567110+c.upper)) = pointBounds65744 := by
 decide +kernel
def cuts65745 : List PrefixCut := [⟨64,187795184,187795291⟩]
theorem checked65745 : checkPrefixCuts (2^48) 8621260801 10 Manual.Count131072.C065745.packed 64 cuts65745 = true := by
 decide +kernel
def cuts65746 : List PrefixCut := [⟨7,20405251,20405263⟩,
⟨64,186519063,186519175⟩]
theorem checked65746 : checkPrefixCuts (2^48) 8621391873 10 Manual.Count131072.C065746.packed 64 cuts65746 = true := by
 decide +kernel
def pointBounds65746 : List (Nat × Nat × Nat) := [(8621406208,115043817918935,115044206974408)]
theorem point_links_checked65746 : (cuts65746.take 1).map (fun c => (8621391873-1+2*2^10*c.k,115043797513684+c.lower,115044186569145+c.upper)) = pointBounds65746 := by
 decide +kernel
def cuts65747 : List PrefixCut := [⟨64,190238051,190238163⟩]
theorem checked65747 : checkPrefixCuts (2^48) 8621522945 10 Manual.Count131072.C065747.packed 64 cuts65747 = true := by
 decide +kernel
def cuts65748 : List PrefixCut := [⟨11,31504734,31504751⟩,
⟨64,186121595,186121695⟩]
theorem checked65748 : checkPrefixCuts (2^48) 8621654017 10 Manual.Count131072.C065748.packed 64 cuts65748 = true := by
 decide +kernel
def pointBounds65748 : List (Nat × Nat × Nat) := [(8621676544,115044205775532,115044594831234)]
theorem point_links_checked65748 : (cuts65748.take 1).map (fun c => (8621654017-1+2*2^10*c.k,115044174270798+c.lower,115044563326483+c.upper)) = pointBounds65748 := by
 decide +kernel
def cuts65749 : List PrefixCut := [⟨64,186804359,186804468⟩]
theorem checked65749 : checkPrefixCuts (2^48) 8621785089 10 Manual.Count131072.C065749.packed 64 cuts65749 = true := by
 decide +kernel
def cuts65750 : List PrefixCut := [⟨15,44431729,44431756⟩,
⟨64,185169228,185169338⟩]
theorem checked65750 : checkPrefixCuts (2^48) 8621916161 10 Manual.Count131072.C065750.packed 64 cuts65750 = true := by
 decide +kernel
def pointBounds65750 : List (Nat × Nat × Nat) := [(8621946880,115044591628481,115044980684402)]
theorem point_links_checked65750 : (cuts65750.take 1).map (fun c => (8621916161-1+2*2^10*c.k,115044547196752+c.lower,115044936252646+c.upper)) = pointBounds65750 := by
 decide +kernel
def cuts65751 : List PrefixCut := [⟨64,187451598,187451709⟩]
theorem checked65751 : checkPrefixCuts (2^48) 8622047233 10 Manual.Count131072.C065751.packed 64 cuts65751 = true := by
 decide +kernel
def cuts65752 : List PrefixCut := [⟨19,55725658,55725690⟩,
⟨64,187220238,187220343⟩]
theorem checked65752 : checkPrefixCuts (2^48) 8622178305 10 Manual.Count131072.C065752.packed 64 cuts65752 = true := by
 decide +kernel
def pointBounds65752 : List (Nat × Nat × Nat) := [(8622217216,115044975543236,115045364599383)]
theorem point_links_checked65752 : (cuts65752.take 1).map (fun c => (8622178305-1+2*2^10*c.k,115044919817578+c.lower,115045308873693+c.upper)) = pointBounds65752 := by
 decide +kernel
def cuts65753 : List PrefixCut := [⟨64,186695066,186695174⟩]
theorem checked65753 : checkPrefixCuts (2^48) 8622309377 10 Manual.Count131072.C065753.packed 64 cuts65753 = true := by
 decide +kernel
def cuts65754 : List PrefixCut := [⟨23,68128800,68128838⟩,
⟨64,189401703,189401807⟩]
theorem checked65754 : checkPrefixCuts (2^48) 8622440449 10 Manual.Count131072.C065754.packed 64 cuts65754 = true := by
 decide +kernel
def pointBounds65754 : List (Nat × Nat × Nat) := [(8622487552,115045361861682,115045750918048)]
theorem point_links_checked65754 : (cuts65754.take 1).map (fun c => (8622440449-1+2*2^10*c.k,115045293732882+c.lower,115045682789210+c.upper)) = pointBounds65754 := by
 decide +kernel
def cuts65755 : List PrefixCut := [⟨64,186852624,186852731⟩]
theorem checked65755 : checkPrefixCuts (2^48) 8622571521 10 Manual.Count131072.C065755.packed 64 cuts65755 = true := by
 decide +kernel
def cuts65756 : List PrefixCut := [⟨27,78539928,78539971⟩,
⟨64,186555988,186556097⟩]
theorem checked65756 : checkPrefixCuts (2^48) 8622702593 10 Manual.Count131072.C065756.packed 64 cuts65756 = true := by
 decide +kernel
def pointBounds65756 : List (Nat × Nat × Nat) := [(8622757888,115045748527137,115046137583719)]
theorem point_links_checked65756 : (cuts65756.take 1).map (fun c => (8622702593-1+2*2^10*c.k,115045669987209+c.lower,115046059043748+c.upper)) = pointBounds65756 := by
 decide +kernel
def cuts65757 : List PrefixCut := [⟨64,187728288,187728400⟩]
theorem checked65757 : checkPrefixCuts (2^48) 8622833665 10 Manual.Count131072.C065757.packed 64 cuts65757 = true := by
 decide +kernel
def cuts65758 : List PrefixCut := [⟨31,91300664,91300718⟩,
⟨64,185212002,185212111⟩]
theorem checked65758 : checkPrefixCuts (2^48) 8622964737 10 Manual.Count131072.C065758.packed 64 cuts65758 = true := by
 decide +kernel
def pointBounds65758 : List (Nat × Nat × Nat) := [(8623028224,115046135572149,115046524628963)]
theorem point_links_checked65758 : (cuts65758.take 1).map (fun c => (8622964737-1+2*2^10*c.k,115046044271485+c.lower,115046433328245+c.upper)) = pointBounds65758 := by
 decide +kernel
def cuts65759 : List PrefixCut := [⟨64,188310122,188310236⟩]
theorem checked65759 : checkPrefixCuts (2^48) 8623095809 10 Manual.Count131072.C065759.packed 64 cuts65759 = true := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S7.B000179
