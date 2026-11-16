import PlattAssemblyKernel
import PlattCertificates.Count131072.C071888
import PlattCertificates.Count131072.C071889
import PlattCertificates.Count131072.C071890
import PlattCertificates.Count131072.C071891
import PlattCertificates.Count131072.C071892
import PlattCertificates.Count131072.C071893
import PlattCertificates.Count131072.C071894
import PlattCertificates.Count131072.C071895
import PlattCertificates.Count131072.C071896
import PlattCertificates.Count131072.C071897
import PlattCertificates.Count131072.C071898
import PlattCertificates.Count131072.C071899
import PlattCertificates.Count131072.C071900
import PlattCertificates.Count131072.C071901
import PlattCertificates.Count131072.C071902
import PlattCertificates.Count131072.C071903
import PlattCertificates.Count131072.C071904
import PlattCertificates.Count131072.C071905
import PlattCertificates.Count131072.C071906
import PlattCertificates.Count131072.C071907
import PlattCertificates.Count131072.C071908
import PlattCertificates.Count131072.C071909
import PlattCertificates.Count131072.C071910
import PlattCertificates.Count131072.C071911
import PlattCertificates.Count131072.C071912
import PlattCertificates.Count131072.C071913
import PlattCertificates.Count131072.C071914
import PlattCertificates.Count131072.C071915
import PlattCertificates.Count131072.C071916
import PlattCertificates.Count131072.C071917
import PlattCertificates.Count131072.C071918
import PlattCertificates.Count131072.C071919
namespace ChenEffective.PlattWindow.Assembly.Prefix.S8.B000059
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts71888 : List PrefixCut := [⟨64,168708731,168708832⟩]
theorem checked71888 : checkPrefixCuts (2^48) 9426436097 10 Manual.Count131072.C071888.packed 64 cuts71888 = true := by
 decide +kernel
def cuts71889 : List PrefixCut := [⟨14,36219816,36219838⟩,
⟨64,168049473,168049577⟩]
theorem checked71889 : checkPrefixCuts (2^48) 9426567169 10 Manual.Count131072.C071889.packed 64 cuts71889 = true := by
 decide +kernel
def pointBounds71889 : List (Nat × Nat × Nat) := [(9426595840,116140201048434,116140590746463)]
theorem point_links_checked71889 : (cuts71889.take 1).map (fun c => (9426567169-1+2*2^10*c.k,116140164828618+c.lower,116140554526625+c.upper)) = pointBounds71889 := by
 decide +kernel
def cuts71890 : List PrefixCut := [⟨64,169390804,169390910⟩]
theorem checked71890 : checkPrefixCuts (2^48) 9426698241 10 Manual.Count131072.C071890.packed 64 cuts71890 = true := by
 decide +kernel
def cuts71891 : List PrefixCut := [⟨30,78916856,78916904⟩,
⟨64,171627845,171627942⟩]
theorem checked71891 : checkPrefixCuts (2^48) 9426829313 10 Manual.Count131072.C071891.packed 64 cuts71891 = true := by
 decide +kernel
def pointBounds71891 : List (Nat × Nat × Nat) := [(9426890752,116140581185751,116140970884016)]
theorem point_links_checked71891 : (cuts71891.take 1).map (fun c => (9426829313-1+2*2^10*c.k,116140502268895+c.lower,116140891967112+c.upper)) = pointBounds71891 := by
 decide +kernel
def cuts71892 : List PrefixCut := [⟨64,170222132,170222234⟩]
theorem checked71892 : checkPrefixCuts (2^48) 9426960385 10 Manual.Count131072.C071892.packed 64 cuts71892 = true := by
 decide +kernel
def cuts71893 : List PrefixCut := [⟨46,123163980,123164052⟩,
⟨64,169443458,169443558⟩]
theorem checked71893 : checkPrefixCuts (2^48) 9427091457 10 Manual.Count131072.C071893.packed 64 cuts71893 = true := by
 decide +kernel
def pointBounds71893 : List (Nat × Nat × Nat) := [(9427185664,116140967282852,116141356981340)]
theorem point_links_checked71893 : (cuts71893.take 1).map (fun c => (9427091457-1+2*2^10*c.k,116140844118872+c.lower,116141233817288+c.upper)) = pointBounds71893 := by
 decide +kernel
def cuts71894 : List PrefixCut := [⟨64,171172835,171172940⟩]
theorem checked71894 : checkPrefixCuts (2^48) 9427222529 10 Manual.Count131072.C071894.packed 64 cuts71894 = true := by
 decide +kernel
def cuts71895 : List PrefixCut := [⟨62,166871070,166871173⟩,
⟨64,172514014,172514120⟩]
theorem checked71895 : checkPrefixCuts (2^48) 9427353601 10 Manual.Count131072.C071895.packed 64 cuts71895 = true := by
 decide +kernel
def pointBounds71895 : List (Nat × Nat × Nat) := [(9427480576,116141351606235,116141741304959)]
theorem point_links_checked71895 : (cuts71895.take 1).map (fun c => (9427353601-1+2*2^10*c.k,116141184735165+c.lower,116141574433786+c.upper)) = pointBounds71895 := by
 decide +kernel
def cuts71896 : List PrefixCut := [⟨64,171347207,171347306⟩]
theorem checked71896 : checkPrefixCuts (2^48) 9427484673 10 Manual.Count131072.C071896.packed 64 cuts71896 = true := by
 decide +kernel
def cuts71897 : List PrefixCut := [⟨64,167881512,167881609⟩]
theorem checked71897 : checkPrefixCuts (2^48) 9427615745 10 Manual.Count131072.C071897.packed 64 cuts71897 = true := by
 decide +kernel
def cuts71898 : List PrefixCut := [⟨14,36454132,36454153⟩,
⟨64,171163307,171163404⟩]
theorem checked71898 : checkPrefixCuts (2^48) 9427746817 10 Manual.Count131072.C071898.packed 64 cuts71898 = true := by
 decide +kernel
def pointBounds71898 : List (Nat × Nat × Nat) := [(9427775488,116141732932030,116142122630974)]
theorem point_links_checked71898 : (cuts71898.take 1).map (fun c => (9427746817-1+2*2^10*c.k,116141696477898+c.lower,116142086176821+c.upper)) = pointBounds71898 := by
 decide +kernel
def cuts71899 : List PrefixCut := [⟨64,172026730,172026837⟩]
theorem checked71899 : checkPrefixCuts (2^48) 9427877889 10 Manual.Count131072.C071899.packed 64 cuts71899 = true := by
 decide +kernel
def cuts71900 : List PrefixCut := [⟨30,79772780,79772825⟩,
⟨64,170919706,170919807⟩]
theorem checked71900 : checkPrefixCuts (2^48) 9428008961 10 Manual.Count131072.C071900.packed 64 cuts71900 = true := by
 decide +kernel
def pointBounds71900 : List (Nat × Nat × Nat) := [(9428070400,116142119440715,116142509139887)]
theorem point_links_checked71900 : (cuts71900.take 1).map (fun c => (9428008961-1+2*2^10*c.k,116142039667935+c.lower,116142429367062+c.upper)) = pointBounds71900 := by
 decide +kernel
def cuts71901 : List PrefixCut := [⟨64,167991587,167991687⟩]
theorem checked71901 : checkPrefixCuts (2^48) 9428140033 10 Manual.Count131072.C071901.packed 64 cuts71901 = true := by
 decide +kernel
def cuts71902 : List PrefixCut := [⟨46,121357316,121357390⟩,
⟨64,169840201,169840302⟩]
theorem checked71902 : checkPrefixCuts (2^48) 9428271105 10 Manual.Count131072.C071902.packed 64 cuts71902 = true := by
 decide +kernel
def pointBounds71902 : List (Nat × Nat × Nat) := [(9428365312,116142499936544,116142889635946)]
theorem point_links_checked71902 : (cuts71902.take 1).map (fun c => (9428271105-1+2*2^10*c.k,116142378579228+c.lower,116142768278556+c.upper)) = pointBounds71902 := by
 decide +kernel
def cuts71903 : List PrefixCut := [⟨64,170196085,170196193⟩]
theorem checked71903 : checkPrefixCuts (2^48) 9428402177 10 Manual.Count131072.C071903.packed 64 cuts71903 = true := by
 decide +kernel
def cuts71904 : List PrefixCut := [⟨62,165297812,165297911⟩,
⟨64,171089316,171089417⟩]
theorem checked71904 : checkPrefixCuts (2^48) 9428533249 10 Manual.Count131072.C071904.packed 64 cuts71904 = true := by
 decide +kernel
def pointBounds71904 : List (Nat × Nat × Nat) := [(9428660224,116142883913326,116143273612962)]
theorem point_links_checked71904 : (cuts71904.take 1).map (fun c => (9428533249-1+2*2^10*c.k,116142718615514+c.lower,116143108315051+c.upper)) = pointBounds71904 := by
 decide +kernel
def cuts71905 : List PrefixCut := [⟨64,167832966,167833072⟩]
theorem checked71905 : checkPrefixCuts (2^48) 9428664321 10 Manual.Count131072.C071905.packed 64 cuts71905 = true := by
 decide +kernel
def cuts71906 : List PrefixCut := [⟨64,170427811,170427917⟩]
theorem checked71906 : checkPrefixCuts (2^48) 9428795393 10 Manual.Count131072.C071906.packed 64 cuts71906 = true := by
 decide +kernel
def cuts71907 : List PrefixCut := [⟨14,37225729,37225750⟩,
⟨64,171022483,171022584⟩]
theorem checked71907 : checkPrefixCuts (2^48) 9428926465 10 Manual.Count131072.C071907.packed 64 cuts71907 = true := by
 decide +kernel
def pointBounds71907 : List (Nat × Nat × Nat) := [(9428955136,116143265191336,116143654891207)]
theorem point_links_checked71907 : (cuts71907.take 1).map (fun c => (9428926465-1+2*2^10*c.k,116143227965607+c.lower,116143617665457+c.upper)) = pointBounds71907 := by
 decide +kernel
def cuts71908 : List PrefixCut := [⟨64,172363432,172363532⟩]
theorem checked71908 : checkPrefixCuts (2^48) 9429057537 10 Manual.Count131072.C071908.packed 64 cuts71908 = true := by
 decide +kernel
def cuts71909 : List PrefixCut := [⟨30,81583732,81583779⟩,
⟨64,170181911,170182014⟩]
theorem checked71909 : checkPrefixCuts (2^48) 9429188609 10 Manual.Count131072.C071909.packed 64 cuts71909 = true := by
 decide +kernel
def pointBounds71909 : List (Nat × Nat × Nat) := [(9429250048,116143652935254,116144042635352)]
theorem point_links_checked71909 : (cuts71909.take 1).map (fun c => (9429188609-1+2*2^10*c.k,116143571351522+c.lower,116143961051573+c.upper)) = pointBounds71909 := by
 decide +kernel
def cuts71910 : List PrefixCut := [⟨64,167522806,167522908⟩]
theorem checked71910 : checkPrefixCuts (2^48) 9429319681 10 Manual.Count131072.C071910.packed 64 cuts71910 = true := by
 decide +kernel
def cuts71911 : List PrefixCut := [⟨46,122954069,122954146⟩,
⟨64,169968224,169968331⟩]
theorem checked71911 : checkPrefixCuts (2^48) 9429450753 10 Manual.Count131072.C071911.packed 64 cuts71911 = true := by
 decide +kernel
def pointBounds71911 : List (Nat × Nat × Nat) := [(9429544960,116144032010308,116144421710641)]
theorem point_links_checked71911 : (cuts71911.take 1).map (fun c => (9429450753-1+2*2^10*c.k,116143909056239+c.lower,116144298756495+c.upper)) = pointBounds71911 := by
 decide +kernel
def cuts71912 : List PrefixCut := [⟨64,169159916,169160007⟩]
theorem checked71912 : checkPrefixCuts (2^48) 9429581825 10 Manual.Count131072.C071912.packed 64 cuts71912 = true := by
 decide +kernel
def cuts71913 : List PrefixCut := [⟨62,164859246,164859338⟩,
⟨64,170142586,170142680⟩]
theorem checked71913 : checkPrefixCuts (2^48) 9429712897 10 Manual.Count131072.C071913.packed 64 cuts71913 = true := by
 decide +kernel
def pointBounds71913 : List (Nat × Nat × Nat) := [(9429839872,116144413043625,116144802744171)]
theorem point_links_checked71913 : (cuts71913.take 1).map (fun c => (9429712897-1+2*2^10*c.k,116144248184379+c.lower,116144637884833+c.upper)) = pointBounds71913 := by
 decide +kernel
def cuts71914 : List PrefixCut := [⟨64,167961233,167961328⟩]
theorem checked71914 : checkPrefixCuts (2^48) 9429843969 10 Manual.Count131072.C071914.packed 64 cuts71914 = true := by
 decide +kernel
def cuts71915 : List PrefixCut := [⟨64,171063171,171063264⟩]
theorem checked71915 : checkPrefixCuts (2^48) 9429975041 10 Manual.Count131072.C071915.packed 64 cuts71915 = true := by
 decide +kernel
def cuts71916 : List PrefixCut := [⟨14,36773343,36773366⟩,
⟨64,168553526,168553632⟩]
theorem checked71916 : checkPrefixCuts (2^48) 9430106113 10 Manual.Count131072.C071916.packed 64 cuts71916 = true := by
 decide +kernel
def pointBounds71916 : List (Nat × Nat × Nat) := [(9430134784,116144794124712,116145183825471)]
theorem point_links_checked71916 : (cuts71916.take 1).map (fun c => (9430106113-1+2*2^10*c.k,116144757351369+c.lower,116145147052105+c.upper)) = pointBounds71916 := by
 decide +kernel
def cuts71917 : List PrefixCut := [⟨64,169506321,169506419⟩]
theorem checked71917 : checkPrefixCuts (2^48) 9430237185 10 Manual.Count131072.C071917.packed 64 cuts71917 = true := by
 decide +kernel
def cuts71918 : List PrefixCut := [⟨30,80618400,80618449⟩,
⟨64,170250154,170250254⟩]
theorem checked71918 : checkPrefixCuts (2^48) 9430368257 10 Manual.Count131072.C071918.packed 64 cuts71918 = true := by
 decide +kernel
def pointBounds71918 : List (Nat × Nat × Nat) := [(9430429696,116145176029616,116145565730605)]
theorem point_links_checked71918 : (cuts71918.take 1).map (fun c => (9430368257-1+2*2^10*c.k,116145095411216+c.lower,116145485112156+c.upper)) = pointBounds71918 := by
 decide +kernel
def cuts71919 : List PrefixCut := [⟨64,172277386,172277491⟩]
theorem checked71919 : checkPrefixCuts (2^48) 9430499329 10 Manual.Count131072.C071919.packed 64 cuts71919 = true := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S8.B000059
