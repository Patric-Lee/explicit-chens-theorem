import PlattAssemblyKernel
import PlattCertificates.Count131072.C040928
import PlattCertificates.Count131072.C040929
import PlattCertificates.Count131072.C040930
import PlattCertificates.Count131072.C040931
import PlattCertificates.Count131072.C040932
import PlattCertificates.Count131072.C040933
import PlattCertificates.Count131072.C040934
import PlattCertificates.Count131072.C040935
import PlattCertificates.Count131072.C040936
import PlattCertificates.Count131072.C040937
import PlattCertificates.Count131072.C040938
import PlattCertificates.Count131072.C040939
import PlattCertificates.Count131072.C040940
import PlattCertificates.Count131072.C040941
import PlattCertificates.Count131072.C040942
import PlattCertificates.Count131072.C040943
import PlattCertificates.Count131072.C040944
import PlattCertificates.Count131072.C040945
import PlattCertificates.Count131072.C040946
import PlattCertificates.Count131072.C040947
import PlattCertificates.Count131072.C040948
import PlattCertificates.Count131072.C040949
import PlattCertificates.Count131072.C040950
import PlattCertificates.Count131072.C040951
import PlattCertificates.Count131072.C040952
import PlattCertificates.Count131072.C040953
import PlattCertificates.Count131072.C040954
import PlattCertificates.Count131072.C040955
import PlattCertificates.Count131072.C040956
import PlattCertificates.Count131072.C040957
import PlattCertificates.Count131072.C040958
import PlattCertificates.Count131072.C040959
namespace ChenEffective.PlattWindow.Assembly.Prefix.S5.B000029
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts40928 : List PrefixCut := [⟨41,196091703,196091820⟩,
⟨64,304989420,304989606⟩]
theorem checked40928 : checkPrefixCuts (2^48) 5368446977 10 Manual.Count131072.C040928.packed 64 cuts40928 = true := by
 decide +kernel
def pointBounds40928 : List (Nat × Nat × Nat) := [(5368530944,109154505956369,109154891632732)]
theorem point_links_checked40928 : (cuts40928.take 1).map (fun c => (5368446977-1+2*2^10*c.k,109154309864666+c.lower,109154695540912+c.upper)) = pointBounds40928 := by
 decide +kernel
def cuts40929 : List PrefixCut := [⟨59,281441411,281441577⟩,
⟨64,304247955,304248134⟩]
theorem checked40929 : checkPrefixCuts (2^48) 5368578049 10 Manual.Count131072.C040929.packed 64 cuts40929 = true := by
 decide +kernel
def pointBounds40929 : List (Nat × Nat × Nat) := [(5368698880,109154896295497,109155281972095)]
theorem point_links_checked40929 : (cuts40929.take 1).map (fun c => (5368578049-1+2*2^10*c.k,109154614854086+c.lower,109155000530518+c.upper)) = pointBounds40929 := by
 decide +kernel
def cuts40930 : List PrefixCut := [⟨64,306914369,306914550⟩]
theorem checked40930 : checkPrefixCuts (2^48) 5368709121 10 Manual.Count131072.C040930.packed 64 cuts40930 = true := by
 decide +kernel
def cuts40931 : List PrefixCut := [⟨13,64538101,64538138⟩,
⟨64,308479689,308479869⟩]
theorem checked40931 : checkPrefixCuts (2^48) 5368840193 10 Manual.Count131072.C040931.packed 64 cuts40931 = true := by
 decide +kernel
def pointBounds40931 : List (Nat × Nat × Nat) := [(5368866816,109155290554511,109155676231340)]
theorem point_links_checked40931 : (cuts40931.take 1).map (fun c => (5368840193-1+2*2^10*c.k,109155226016410+c.lower,109155611693202+c.upper)) = pointBounds40931 := by
 decide +kernel
def cuts40932 : List PrefixCut := [⟨31,149728407,149728494⟩,
⟨64,307476065,307476246⟩]
theorem checked40932 : checkPrefixCuts (2^48) 5368971265 10 Manual.Count131072.C040932.packed 64 cuts40932 = true := by
 decide +kernel
def pointBounds40932 : List (Nat × Nat × Nat) := [(5369034752,109155684224506,109156069901565)]
theorem point_links_checked40932 : (cuts40932.take 1).map (fun c => (5368971265-1+2*2^10*c.k,109155534496099+c.lower,109155920173071+c.upper)) = pointBounds40932 := by
 decide +kernel
def cuts40933 : List PrefixCut := [⟨49,234232467,234232604⟩,
⟨64,306577331,306577511⟩]
theorem checked40933 : checkPrefixCuts (2^48) 5369102337 10 Manual.Count131072.C040933.packed 64 cuts40933 = true := by
 decide +kernel
def pointBounds40933 : List (Nat × Nat × Nat) := [(5369202688,109156076204631,109156461881921)]
theorem point_links_checked40933 : (cuts40933.take 1).map (fun c => (5369102337-1+2*2^10*c.k,109155841972164+c.lower,109156227649317+c.upper)) = pointBounds40933 := by
 decide +kernel
def cuts40934 : List PrefixCut := [⟨64,308142523,308142707⟩]
theorem checked40934 : checkPrefixCuts (2^48) 5369233409 10 Manual.Count131072.C040934.packed 64 cuts40934 = true := by
 decide +kernel
def cuts40935 : List PrefixCut := [⟨3,14311302,14311311⟩,
⟨64,307820449,307820630⟩]
theorem checked40935 : checkPrefixCuts (2^48) 5369364481 10 Manual.Count131072.C040935.packed 64 cuts40935 = true := by
 decide +kernel
def pointBounds40935 : List (Nat × Nat × Nat) := [(5369370624,109156471003320,109156856680846)]
theorem point_links_checked40935 : (cuts40935.take 1).map (fun c => (5369364481-1+2*2^10*c.k,109156456692018+c.lower,109156842369535+c.upper)) = pointBounds40935 := by
 decide +kernel
def cuts40936 : List PrefixCut := [⟨21,102011068,102011125⟩,
⟨64,308022674,308022849⟩]
theorem checked40936 : checkPrefixCuts (2^48) 5369495553 10 Manual.Count131072.C040936.packed 64 cuts40936 = true := by
 decide +kernel
def pointBounds40936 : List (Nat × Nat × Nat) := [(5369538560,109156866523535,109157252201290)]
theorem point_links_checked40936 : (cuts40936.take 1).map (fun c => (5369495553-1+2*2^10*c.k,109156764512467+c.lower,109157150190165+c.upper)) = pointBounds40936 := by
 decide +kernel
def cuts40937 : List PrefixCut := [⟨39,186508349,186508458⟩,
⟨64,307019165,307019345⟩]
theorem checked40937 : checkPrefixCuts (2^48) 5369626625 10 Manual.Count131072.C040937.packed 64 cuts40937 = true := by
 decide +kernel
def pointBounds40937 : List (Nat × Nat × Nat) := [(5369706496,109157259043490,109157644721472)]
theorem point_links_checked40937 : (cuts40937.take 1).map (fun c => (5369626625-1+2*2^10*c.k,109157072535141+c.lower,109157458213014+c.upper)) = pointBounds40937 := by
 decide +kernel
def cuts40938 : List PrefixCut := [⟨57,273150068,273150232⟩,
⟨64,307850345,307850529⟩]
theorem checked40938 : checkPrefixCuts (2^48) 5369757697 10 Manual.Count131072.C040938.packed 64 cuts40938 = true := by
 decide +kernel
def pointBounds40938 : List (Nat × Nat × Nat) := [(5369874432,109157652704374,109158038382591)]
theorem point_links_checked40938 : (cuts40938.take 1).map (fun c => (5369757697-1+2*2^10*c.k,109157379554306+c.lower,109157765232359+c.upper)) = pointBounds40938 := by
 decide +kernel
def cuts40939 : List PrefixCut := [⟨64,302863258,302863444⟩]
theorem checked40939 : checkPrefixCuts (2^48) 5369888769 10 Manual.Count131072.C040939.packed 64 cuts40939 = true := by
 decide +kernel
def cuts40940 : List PrefixCut := [⟨11,54669762,54669793⟩,
⟨64,308726412,308726593⟩]
theorem checked40940 : checkPrefixCuts (2^48) 5370019841 10 Manual.Count131072.C040940.packed 64 cuts40940 = true := by
 decide +kernel
def pointBounds40940 : List (Nat × Nat × Nat) := [(5370042368,109158044937671,109158430616125)]
theorem point_links_checked40940 : (cuts40940.take 1).map (fun c => (5370019841-1+2*2^10*c.k,109157990267909+c.lower,109158375946332+c.upper)) = pointBounds40940 := by
 decide +kernel
def cuts40941 : List PrefixCut := [⟨29,137640266,137640346⟩,
⟨64,304787808,304787985⟩]
theorem checked40941 : checkPrefixCuts (2^48) 5370150913 10 Manual.Count131072.C040941.packed 64 cuts40941 = true := by
 decide +kernel
def pointBounds40941 : List (Nat × Nat × Nat) := [(5370210304,109158436634587,109158822313271)]
theorem point_links_checked40941 : (cuts40941.take 1).map (fun c => (5370150913-1+2*2^10*c.k,109158298994321+c.lower,109158684672925+c.upper)) = pointBounds40941 := by
 decide +kernel
def cuts40942 : List PrefixCut := [⟨47,222807487,222807620⟩,
⟨64,302683860,302684038⟩]
theorem checked40942 : checkPrefixCuts (2^48) 5370281985 10 Manual.Count131072.C040942.packed 64 cuts40942 = true := by
 decide +kernel
def pointBounds40942 : List (Nat × Nat × Nat) := [(5370378240,109158826589616,109159212268530)]
theorem point_links_checked40942 : (cuts40942.take 1).map (fun c => (5370281985-1+2*2^10*c.k,109158603782129+c.lower,109158989460910+c.upper)) = pointBounds40942 := by
 decide +kernel
def cuts40943 : List PrefixCut := [⟨64,306240441,306240619⟩]
theorem checked40943 : checkPrefixCuts (2^48) 5370413057 10 Manual.Count131072.C040943.packed 64 cuts40943 = true := by
 decide +kernel
def cuts40944 : List PrefixCut := [⟨1,4245280,4245282⟩,
⟨64,308643812,308643995⟩]
theorem checked40944 : checkPrefixCuts (2^48) 5370544129 10 Manual.Count131072.C040944.packed 64 cuts40944 = true := by
 decide +kernel
def pointBounds40944 : List (Nat × Nat × Nat) := [(5370546176,109159216951710,109159602630849)]
theorem point_links_checked40944 : (cuts40944.take 1).map (fun c => (5370544129-1+2*2^10*c.k,109159212706430+c.lower,109159598385567+c.upper)) = pointBounds40944 := by
 decide +kernel
def cuts40945 : List PrefixCut := [⟨19,88519476,88519531⟩,
⟨64,302556876,302557053⟩]
theorem checked40945 : checkPrefixCuts (2^48) 5370675201 10 Manual.Count131072.C040945.packed 64 cuts40945 = true := by
 decide +kernel
def pointBounds40945 : List (Nat × Nat × Nat) := [(5370714112,109159609869718,109159995549093)]
theorem point_links_checked40945 : (cuts40945.take 1).map (fun c => (5370675201-1+2*2^10*c.k,109159521350242+c.lower,109159907029562+c.upper)) = pointBounds40945 := by
 decide +kernel
def cuts40946 : List PrefixCut := [⟨37,175409388,175409495⟩,
⟨64,307580618,307580802⟩]
theorem checked40946 : checkPrefixCuts (2^48) 5370806273 10 Manual.Count131072.C040946.packed 64 cuts40946 = true := by
 decide +kernel
def pointBounds40946 : List (Nat × Nat × Nat) := [(5370882048,109159999316506,109160384996110)]
theorem point_links_checked40946 : (cuts40946.take 1).map (fun c => (5370806273-1+2*2^10*c.k,109159823907118+c.lower,109160209586615+c.upper)) = pointBounds40946 := by
 decide +kernel
def cuts40947 : List PrefixCut := [⟨55,264338309,264338465⟩,
⟨64,307363509,307363690⟩]
theorem checked40947 : checkPrefixCuts (2^48) 5370937345 10 Manual.Count131072.C040947.packed 64 cuts40947 = true := by
 decide +kernel
def pointBounds40947 : List (Nat × Nat × Nat) := [(5371049984,109160395826045,109160781505882)]
theorem point_links_checked40947 : (cuts40947.take 1).map (fun c => (5370937345-1+2*2^10*c.k,109160131487736+c.lower,109160517167417+c.upper)) = pointBounds40947 := by
 decide +kernel
def cuts40948 : List PrefixCut := [⟨64,304316495,304316670⟩]
theorem checked40948 : checkPrefixCuts (2^48) 5371068417 10 Manual.Count131072.C040948.packed 64 cuts40948 = true := by
 decide +kernel
def cuts40949 : List PrefixCut := [⟨9,44072086,44072112⟩,
⟨64,305252370,305252551⟩]
theorem checked40949 : checkPrefixCuts (2^48) 5371199489 10 Manual.Count131072.C040949.packed 64 cuts40949 = true := by
 decide +kernel
def pointBounds40949 : List (Nat × Nat × Nat) := [(5371217920,109160787239826,109161172919889)]
theorem point_links_checked40949 : (cuts40949.take 1).map (fun c => (5371199489-1+2*2^10*c.k,109160743167740+c.lower,109161128847777+c.upper)) = pointBounds40949 := by
 decide +kernel
def cuts40950 : List PrefixCut := [⟨27,127339116,127339192⟩,
⟨64,307236165,307236344⟩]
theorem checked40950 : checkPrefixCuts (2^48) 5371330561 10 Manual.Count131072.C040950.packed 64 cuts40950 = true := by
 decide +kernel
def pointBounds40950 : List (Nat × Nat × Nat) := [(5371385856,109161175759226,109161561439520)]
theorem point_links_checked40950 : (cuts40950.take 1).map (fun c => (5371330561-1+2*2^10*c.k,109161048420110+c.lower,109161434100328+c.upper)) = pointBounds40950 := by
 decide +kernel
def cuts40951 : List PrefixCut := [⟨45,216575276,216575407⟩,
⟨64,308067126,308067315⟩]
theorem checked40951 : checkPrefixCuts (2^48) 5371461633 10 Manual.Count131072.C040951.packed 64 cuts40951 = true := by
 decide +kernel
def pointBounds40951 : List (Nat × Nat × Nat) := [(5371553792,109161572231551,109161957912079)]
theorem point_links_checked40951 : (cuts40951.take 1).map (fun c => (5371461633-1+2*2^10*c.k,109161355656275+c.lower,109161741336672+c.upper)) = pointBounds40951 := by
 decide +kernel
def cuts40952 : List PrefixCut := [⟨63,301038079,301038259⟩,
⟨64,306487614,306487797⟩]
theorem checked40952 : checkPrefixCuts (2^48) 5371592705 10 Manual.Count131072.C040952.packed 64 cuts40952 = true := by
 decide +kernel
def pointBounds40952 : List (Nat × Nat × Nat) := [(5371721728,109161964761480,109162350442246)]
theorem point_links_checked40952 : (cuts40952.take 1).map (fun c => (5371592705-1+2*2^10*c.k,109161663723401+c.lower,109162049403987+c.upper)) = pointBounds40952 := by
 decide +kernel
def cuts40953 : List PrefixCut := [⟨64,307475665,307475850⟩]
theorem checked40953 : checkPrefixCuts (2^48) 5371723777 10 Manual.Count131072.C040953.packed 64 cuts40953 = true := by
 decide +kernel
def cuts40954 : List PrefixCut := [⟨17,80902380,80902430⟩,
⟨64,307625383,307625565⟩]
theorem checked40954 : checkPrefixCuts (2^48) 5371854849 10 Manual.Count131072.C040954.packed 64 cuts40954 = true := by
 decide +kernel
def pointBounds40954 : List (Nat × Nat × Nat) := [(5371889664,109162358589060,109162744270064)]
theorem point_links_checked40954 : (cuts40954.take 1).map (fun c => (5371854849-1+2*2^10*c.k,109162277686680+c.lower,109162663367634+c.upper)) = pointBounds40954 := by
 decide +kernel
def cuts40955 : List PrefixCut := [⟨35,166620733,166620833⟩,
⟨64,300701618,300701801⟩]
theorem checked40955 : checkPrefixCuts (2^48) 5371985921 10 Manual.Count131072.C040955.packed 64 cuts40955 = true := by
 decide +kernel
def pointBounds40955 : List (Nat × Nat × Nat) := [(5372057600,109162751932796,109163137614032)]
theorem point_links_checked40955 : (cuts40955.take 1).map (fun c => (5371985921-1+2*2^10*c.k,109162585312063+c.lower,109162970993199+c.upper)) = pointBounds40955 := by
 decide +kernel
def cuts40956 : List PrefixCut := [⟨53,253120225,253120379⟩,
⟨64,305095431,305095615⟩]
theorem checked40956 : checkPrefixCuts (2^48) 5372116993 10 Manual.Count131072.C040956.packed 64 cuts40956 = true := by
 decide +kernel
def pointBounds40956 : List (Nat × Nat × Nat) := [(5372225536,109163139133906,109163524815379)]
theorem point_links_checked40956 : (cuts40956.take 1).map (fun c => (5372116993-1+2*2^10*c.k,109162886013681+c.lower,109163271695000+c.upper)) = pointBounds40956 := by
 decide +kernel
def cuts40957 : List PrefixCut := [⟨64,308231555,308231736⟩]
theorem checked40957 : checkPrefixCuts (2^48) 5372248065 10 Manual.Count131072.C040957.packed 64 cuts40957 = true := by
 decide +kernel
def cuts40958 : List PrefixCut := [⟨7,34631707,34631728⟩,
⟨64,309848246,309848421⟩]
theorem checked40958 : checkPrefixCuts (2^48) 5372379137 10 Manual.Count131072.C040958.packed 64 cuts40958 = true := by
 decide +kernel
def pointBounds40958 : List (Nat × Nat × Nat) := [(5372393472,109163533972374,109163919654079)]
theorem point_links_checked40958 : (cuts40958.take 1).map (fun c => (5372379137-1+2*2^10*c.k,109163499340667+c.lower,109163885022351+c.upper)) = pointBounds40958 := by
 decide +kernel
def cuts40959 : List PrefixCut := [⟨25,120447927,120447994⟩,
⟨64,304863537,304863717⟩]
theorem checked40959 : checkPrefixCuts (2^48) 5372510209 10 Manual.Count131072.C040959.packed 64 cuts40959 = true := by
 decide +kernel
def pointBounds40959 : List (Nat × Nat × Nat) := [(5372561408,109163929636840,109164315318766)]
theorem point_links_checked40959 : (cuts40959.take 1).map (fun c => (5372510209-1+2*2^10*c.k,109163809188913+c.lower,109164194870772+c.upper)) = pointBounds40959 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S5.B000029
