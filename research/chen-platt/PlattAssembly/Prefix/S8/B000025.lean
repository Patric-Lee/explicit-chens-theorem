import PlattAssemblyKernel
import PlattCertificates.Count131072.C070800
import PlattCertificates.Count131072.C070801
import PlattCertificates.Count131072.C070802
import PlattCertificates.Count131072.C070803
import PlattCertificates.Count131072.C070804
import PlattCertificates.Count131072.C070805
import PlattCertificates.Count131072.C070806
import PlattCertificates.Count131072.C070807
import PlattCertificates.Count131072.C070808
import PlattCertificates.Count131072.C070809
import PlattCertificates.Count131072.C070810
import PlattCertificates.Count131072.C070811
import PlattCertificates.Count131072.C070812
import PlattCertificates.Count131072.C070813
import PlattCertificates.Count131072.C070814
import PlattCertificates.Count131072.C070815
import PlattCertificates.Count131072.C070816
import PlattCertificates.Count131072.C070817
import PlattCertificates.Count131072.C070818
import PlattCertificates.Count131072.C070819
import PlattCertificates.Count131072.C070820
import PlattCertificates.Count131072.C070821
import PlattCertificates.Count131072.C070822
import PlattCertificates.Count131072.C070823
import PlattCertificates.Count131072.C070824
import PlattCertificates.Count131072.C070825
import PlattCertificates.Count131072.C070826
import PlattCertificates.Count131072.C070827
import PlattCertificates.Count131072.C070828
import PlattCertificates.Count131072.C070829
import PlattCertificates.Count131072.C070830
import PlattCertificates.Count131072.C070831
namespace ChenEffective.PlattWindow.Assembly.Prefix.S8.B000025
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts70800 : List PrefixCut := [⟨64,174059189,174059291⟩]
theorem checked70800 : checkPrefixCuts (2^48) 9283829761 10 Manual.Count131072.C070800.packed 64 cuts70800 = true := by
 decide +kernel
def cuts70801 : List PrefixCut := [⟨39,105386325,105386388⟩,
⟨64,172571150,172571252⟩]
theorem checked70801 : checkPrefixCuts (2^48) 9283960833 10 Manual.Count131072.C070801.packed 64 cuts70801 = true := by
 decide +kernel
def pointBounds70801 : List (Nat × Nat × Nat) := [(9284040704,115953382012939,115953771600363)]
theorem point_links_checked70801 : (cuts70801.take 1).map (fun c => (9283960833-1+2*2^10*c.k,115953276626614+c.lower,115953666213975+c.upper)) = pointBounds70801 := by
 decide +kernel
def cuts70802 : List PrefixCut := [⟨64,172568710,172568809⟩]
theorem checked70802 : checkPrefixCuts (2^48) 9284091905 10 Manual.Count131072.C070802.packed 64 cuts70802 = true := by
 decide +kernel
def cuts70803 : List PrefixCut := [⟨53,143492121,143492203⟩,
⟨64,173142302,173142403⟩]
theorem checked70803 : checkPrefixCuts (2^48) 9284222977 10 Manual.Count131072.C070803.packed 64 cuts70803 = true := by
 decide +kernel
def pointBounds70803 : List (Nat × Nat × Nat) := [(9284331520,115953765258595,115954154846239)]
theorem point_links_checked70803 : (cuts70803.take 1).map (fun c => (9284222977-1+2*2^10*c.k,115953621766474+c.lower,115954011354036+c.upper)) = pointBounds70803 := by
 decide +kernel
def cuts70804 : List PrefixCut := [⟨64,174716327,174716426⟩]
theorem checked70804 : checkPrefixCuts (2^48) 9284354049 10 Manual.Count131072.C070804.packed 64 cuts70804 = true := by
 decide +kernel
def cuts70805 : List PrefixCut := [⟨64,174289447,174289547⟩]
theorem checked70805 : checkPrefixCuts (2^48) 9284485121 10 Manual.Count131072.C070805.packed 64 cuts70805 = true := by
 decide +kernel
def cuts70806 : List PrefixCut := [⟨3,8549184,8549190⟩,
⟨64,174347618,174347725⟩]
theorem checked70806 : checkPrefixCuts (2^48) 9284616193 10 Manual.Count131072.C070806.packed 64 cuts70806 = true := by
 decide +kernel
def pointBounds70806 : List (Nat × Nat × Nat) := [(9284622336,115954152463734,115954542051602)]
theorem point_links_checked70806 : (cuts70806.take 1).map (fun c => (9284616193-1+2*2^10*c.k,115954143914550+c.lower,115954533502412+c.upper)) = pointBounds70806 := by
 decide +kernel
def cuts70807 : List PrefixCut := [⟨64,171343900,171344001⟩]
theorem checked70807 : checkPrefixCuts (2^48) 9284747265 10 Manual.Count131072.C070807.packed 64 cuts70807 = true := by
 decide +kernel
def cuts70808 : List PrefixCut := [⟨17,44927353,44927380⟩,
⟨64,170432023,170432133⟩]
theorem checked70808 : checkPrefixCuts (2^48) 9284878337 10 Manual.Count131072.C070808.packed 64 cuts70808 = true := by
 decide +kernel
def pointBounds70808 : List (Nat × Nat × Nat) := [(9284913152,115954534533421,115954924121518)]
theorem point_links_checked70808 : (cuts70808.take 1).map (fun c => (9284878337-1+2*2^10*c.k,115954489606068+c.lower,115954879194138+c.upper)) = pointBounds70808 := by
 decide +kernel
def cuts70809 : List PrefixCut := [⟨64,175158730,175158835⟩]
theorem checked70809 : checkPrefixCuts (2^48) 9285009409 10 Manual.Count131072.C070809.packed 64 cuts70809 = true := by
 decide +kernel
def cuts70810 : List PrefixCut := [⟨31,84243859,84243909⟩,
⟨64,173670861,173670965⟩]
theorem checked70810 : checkPrefixCuts (2^48) 9285140481 10 Manual.Count131072.C070810.packed 64 cuts70810 = true := by
 decide +kernel
def pointBounds70810 : List (Nat × Nat × Nat) := [(9285203968,115954919440680,115955309029015)]
theorem point_links_checked70810 : (cuts70810.take 1).map (fun c => (9285140481-1+2*2^10*c.k,115954835196821+c.lower,115955224785106+c.upper)) = pointBounds70810 := by
 decide +kernel
def cuts70811 : List PrefixCut := [⟨64,172001141,172001243⟩]
theorem checked70811 : checkPrefixCuts (2^48) 9285271553 10 Manual.Count131072.C070811.packed 64 cuts70811 = true := by
 decide +kernel
def cuts70812 : List PrefixCut := [⟨45,124164289,124164363⟩,
⟨64,176060718,176060823⟩]
theorem checked70812 : checkPrefixCuts (2^48) 9285402625 10 Manual.Count131072.C070812.packed 64 cuts70812 = true := by
 decide +kernel
def pointBounds70812 : List (Nat × Nat × Nat) := [(9285494784,115955305033112,115955694621677)]
theorem point_links_checked70812 : (cuts70812.take 1).map (fun c => (9285402625-1+2*2^10*c.k,115955180868823+c.lower,115955570457314+c.upper)) = pointBounds70812 := by
 decide +kernel
def cuts70813 : List PrefixCut := [⟨64,173845370,173845473⟩]
theorem checked70813 : checkPrefixCuts (2^48) 9285533697 10 Manual.Count131072.C070813.packed 64 cuts70813 = true := by
 decide +kernel
def cuts70814 : List PrefixCut := [⟨59,159596080,159596171⟩,
⟨64,172963861,172963961⟩]
theorem checked70814 : checkPrefixCuts (2^48) 9285664769 10 Manual.Count131072.C070814.packed 64 cuts70814 = true := by
 decide +kernel
def pointBounds70814 : List (Nat × Nat × Nat) := [(9285785600,115955690370991,115956079959781)]
theorem point_links_checked70814 : (cuts70814.take 1).map (fun c => (9285664769-1+2*2^10*c.k,115955530774911+c.lower,115955920363610+c.upper)) = pointBounds70814 := by
 decide +kernel
def cuts70815 : List PrefixCut := [⟨64,172991737,172991836⟩]
theorem checked70815 : checkPrefixCuts (2^48) 9285795841 10 Manual.Count131072.C070815.packed 64 cuts70815 = true := by
 decide +kernel
def cuts70816 : List PrefixCut := [⟨64,171746514,171746614⟩]
theorem checked70816 : checkPrefixCuts (2^48) 9285926913 10 Manual.Count131072.C070816.packed 64 cuts70816 = true := by
 decide +kernel
def cuts70817 : List PrefixCut := [⟨9,24309848,24309861⟩,
⟨64,171531905,171532006⟩]
theorem checked70817 : checkPrefixCuts (2^48) 9286057985 10 Manual.Count131072.C070817.packed 64 cuts70817 = true := by
 decide +kernel
def pointBounds70817 : List (Nat × Nat × Nat) := [(9286076416,115956072786871,115956462375882)]
theorem point_links_checked70817 : (cuts70817.take 1).map (fun c => (9286057985-1+2*2^10*c.k,115956048477023+c.lower,115956438066021+c.upper)) = pointBounds70817 := by
 decide +kernel
def cuts70818 : List PrefixCut := [⟨64,174136214,174136321⟩]
theorem checked70818 : checkPrefixCuts (2^48) 9286189057 10 Manual.Count131072.C070818.packed 64 cuts70818 = true := by
 decide +kernel
def cuts70819 : List PrefixCut := [⟨23,63379519,63379557⟩,
⟨64,174194386,174194488⟩]
theorem checked70819 : checkPrefixCuts (2^48) 9286320129 10 Manual.Count131072.C070819.packed 64 cuts70819 = true := by
 decide +kernel
def pointBounds70819 : List (Nat × Nat × Nat) := [(9286367232,115956457524661,115956847113905)]
theorem point_links_checked70819 : (cuts70819.take 1).map (fun c => (9286320129-1+2*2^10*c.k,115956394145142+c.lower,115956783734348+c.upper)) = pointBounds70819 := by
 decide +kernel
def cuts70820 : List PrefixCut := [⟨64,175343704,175343810⟩]
theorem checked70820 : checkPrefixCuts (2^48) 9286451201 10 Manual.Count131072.C070820.packed 64 cuts70820 = true := by
 decide +kernel
def cuts70821 : List PrefixCut := [⟨37,97930718,97930775⟩,
⟨64,172583040,172583142⟩]
theorem checked70821 : checkPrefixCuts (2^48) 9286582273 10 Manual.Count131072.C070821.packed 64 cuts70821 = true := by
 decide +kernel
def pointBounds70821 : List (Nat × Nat × Nat) := [(9286658048,115956841613950,115957231203421)]
theorem point_links_checked70821 : (cuts70821.take 1).map (fun c => (9286582273-1+2*2^10*c.k,115956743683232+c.lower,115957133272646+c.upper)) = pointBounds70821 := by
 decide +kernel
def cuts70822 : List PrefixCut := [⟨64,171307623,171307726⟩]
theorem checked70822 : checkPrefixCuts (2^48) 9286713345 10 Manual.Count131072.C070822.packed 64 cuts70822 = true := by
 decide +kernel
def cuts70823 : List PrefixCut := [⟨51,137692977,137693060⟩,
⟨64,174093615,174093720⟩]
theorem checked70823 : checkPrefixCuts (2^48) 9286844417 10 Manual.Count131072.C070823.packed 64 cuts70823 = true := by
 decide +kernel
def pointBounds70823 : List (Nat × Nat × Nat) := [(9286948864,115957225266872,115957614856574)]
theorem point_links_checked70823 : (cuts70823.take 1).map (fun c => (9286844417-1+2*2^10*c.k,115957087573895+c.lower,115957477163514+c.upper)) = pointBounds70823 := by
 decide +kernel
def cuts70824 : List PrefixCut := [⟨64,174060861,174060966⟩]
theorem checked70824 : checkPrefixCuts (2^48) 9286975489 10 Manual.Count131072.C070824.packed 64 cuts70824 = true := by
 decide +kernel
def cuts70825 : List PrefixCut := [⟨64,172421771,172421871⟩]
theorem checked70825 : checkPrefixCuts (2^48) 9287106561 10 Manual.Count131072.C070825.packed 64 cuts70825 = true := by
 decide +kernel
def cuts70826 : List PrefixCut := [⟨1,2788309,2788311⟩,
⟨64,172298114,172298211⟩]
theorem checked70826 : checkPrefixCuts (2^48) 9287237633 10 Manual.Count131072.C070826.packed 64 cuts70826 = true := by
 decide +kernel
def pointBounds70826 : List (Nat × Nat × Nat) := [(9287239680,115957610938451,115958000528382)]
theorem point_links_checked70826 : (cuts70826.take 1).map (fun c => (9287237633-1+2*2^10*c.k,115957608150142+c.lower,115957997740071+c.upper)) = pointBounds70826 := by
 decide +kernel
def cuts70827 : List PrefixCut := [⟨64,174235329,174235428⟩]
theorem checked70827 : checkPrefixCuts (2^48) 9287368705 10 Manual.Count131072.C070827.packed 64 cuts70827 = true := by
 decide +kernel
def cuts70828 : List PrefixCut := [⟨15,41217250,41217276⟩,
⟨64,173869183,173869289⟩]
theorem checked70828 : checkPrefixCuts (2^48) 9287499777 10 Manual.Count131072.C070828.packed 64 cuts70828 = true := by
 decide +kernel
def pointBounds70828 : List (Nat × Nat × Nat) := [(9287530496,115957995900835,115958385490986)]
theorem point_links_checked70828 : (cuts70828.take 1).map (fun c => (9287499777-1+2*2^10*c.k,115957954683585+c.lower,115958344273710+c.upper)) = pointBounds70828 := by
 decide +kernel
def cuts70829 : List PrefixCut := [⟨64,174533468,174533570⟩]
theorem checked70829 : checkPrefixCuts (2^48) 9287630849 10 Manual.Count131072.C070829.packed 64 cuts70829 = true := by
 decide +kernel
def cuts70830 : List PrefixCut := [⟨29,78522593,78522638⟩,
⟨64,173591535,173591634⟩]
theorem checked70830 : checkPrefixCuts (2^48) 9287761921 10 Manual.Count131072.C070830.packed 64 cuts70830 = true := by
 decide +kernel
def pointBounds70830 : List (Nat × Nat × Nat) := [(9287821312,115958381608829,115958771199207)]
theorem point_links_checked70830 : (cuts70830.take 1).map (fun c => (9287761921-1+2*2^10*c.k,115958303086236+c.lower,115958692676569+c.upper)) = pointBounds70830 := by
 decide +kernel
def cuts70831 : List PrefixCut := [⟨64,171164653,171164752⟩]
theorem checked70831 : checkPrefixCuts (2^48) 9287892993 10 Manual.Count131072.C070831.packed 64 cuts70831 = true := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S8.B000025
