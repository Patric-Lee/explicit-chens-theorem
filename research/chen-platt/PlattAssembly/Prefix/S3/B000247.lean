import PlattAssemblyKernel
import PlattCertificates.Count131072.C027904
import PlattCertificates.Count131072.C027905
import PlattCertificates.Count131072.C027906
import PlattCertificates.Count131072.C027907
import PlattCertificates.Count131072.C027908
import PlattCertificates.Count131072.C027909
import PlattCertificates.Count131072.C027910
import PlattCertificates.Count131072.C027911
import PlattCertificates.Count131072.C027912
import PlattCertificates.Count131072.C027913
import PlattCertificates.Count131072.C027914
import PlattCertificates.Count131072.C027915
import PlattCertificates.Count131072.C027916
import PlattCertificates.Count131072.C027917
import PlattCertificates.Count131072.C027918
import PlattCertificates.Count131072.C027919
import PlattCertificates.Count131072.C027920
import PlattCertificates.Count131072.C027921
import PlattCertificates.Count131072.C027922
import PlattCertificates.Count131072.C027923
import PlattCertificates.Count131072.C027924
import PlattCertificates.Count131072.C027925
import PlattCertificates.Count131072.C027926
import PlattCertificates.Count131072.C027927
import PlattCertificates.Count131072.C027928
import PlattCertificates.Count131072.C027929
import PlattCertificates.Count131072.C027930
import PlattCertificates.Count131072.C027931
import PlattCertificates.Count131072.C027932
import PlattCertificates.Count131072.C027933
import PlattCertificates.Count131072.C027934
import PlattCertificates.Count131072.C027935
namespace ChenEffective.PlattWindow.Assembly.Prefix.S3.B000247
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts27904 : List PrefixCut := [⟨60,215177010,215177128⟩,
⟨128,460177672,460177926⟩]
theorem checked27904 : checkPrefixCuts (2^48) 3661365249 9 Manual.Count131072.C027904.packed 128 cuts27904 = true := by
 decide +kernel
def pointBounds27904 : List (Nat × Nat × Nat) := [(3661426688,104304901848688,104305284652755)]
theorem point_links_checked27904 : (cuts27904.take 1).map (fun c => (3661365249-1+2*2^9*c.k,104304686671678+c.lower,104305069475627+c.upper)) = pointBounds27904 := by
 decide +kernel
def cuts27905 : List PrefixCut := [⟨44,156130715,156130809⟩,
⟨128,456778755,456779016⟩]
theorem checked27905 : checkPrefixCuts (2^48) 3661496321 9 Manual.Count131072.C027905.packed 128 cuts27905 = true := by
 decide +kernel
def pointBounds27905 : List (Nat × Nat × Nat) := [(3661541376,104305302980065,104305685784362)]
theorem point_links_checked27905 : (cuts27905.take 1).map (fun c => (3661496321-1+2*2^9*c.k,104305146849350+c.lower,104305529653553+c.upper)) = pointBounds27905 := by
 decide +kernel
def cuts27906 : List PrefixCut := [⟨28,97395844,97395900⟩,
⟨128,453533905,453534159⟩]
theorem checked27906 : checkPrefixCuts (2^48) 3661627393 9 Manual.Count131072.C027906.packed 128 cuts27906 = true := by
 decide +kernel
def pointBounds27906 : List (Nat × Nat × Nat) := [(3661656064,104305701023949,104306083828469)]
theorem point_links_checked27906 : (cuts27906.take 1).map (fun c => (3661627393-1+2*2^9*c.k,104305603628105+c.lower,104305986432569+c.upper)) = pointBounds27906 := by
 decide +kernel
def cuts27907 : List PrefixCut := [⟨12,43046444,43046468⟩,
⟨124,437606395,437606644⟩,
⟨128,449981832,449982088⟩]
theorem checked27907 : checkPrefixCuts (2^48) 3661758465 9 Manual.Count131072.C027907.packed 128 cuts27907 = true := by
 decide +kernel
def pointBounds27907 : List (Nat × Nat × Nat) := [(3661770752,104306100208454,104306483013196),(3661885440,104306494768405,104306877573372)]
theorem point_links_checked27907 : (cuts27907.take 2).map (fun c => (3661758465-1+2*2^9*c.k,104306057162010+c.lower,104306439966728+c.upper)) = pointBounds27907 := by
 decide +kernel
def cuts27908 : List PrefixCut := [⟨108,384247444,384247660⟩,
⟨128,455115585,455115841⟩]
theorem checked27908 : checkPrefixCuts (2^48) 3661889537 9 Manual.Count131072.C027908.packed 128 cuts27908 = true := by
 decide +kernel
def pointBounds27908 : List (Nat × Nat × Nat) := [(3662000128,104306891391286,104307274196476)]
theorem point_links_checked27908 : (cuts27908.take 1).map (fun c => (3661889537-1+2*2^9*c.k,104306507143842+c.lower,104306889948816+c.upper)) = pointBounds27908 := by
 decide +kernel
def cuts27909 : List PrefixCut := [⟨92,334197234,334197418⟩,
⟨128,460633446,460633700⟩]
theorem checked27909 : checkPrefixCuts (2^48) 3662020609 9 Manual.Count131072.C027909.packed 128 cuts27909 = true := by
 decide +kernel
def pointBounds27909 : List (Nat × Nat × Nat) := [(3662114816,104307296456661,104307679262075)]
theorem point_links_checked27909 : (cuts27909.take 1).map (fun c => (3662020609-1+2*2^9*c.k,104306962259427+c.lower,104307345064657+c.upper)) = pointBounds27909 := by
 decide +kernel
def cuts27910 : List PrefixCut := [⟨76,274389160,274389309⟩,
⟨128,454775657,454775909⟩]
theorem checked27910 : checkPrefixCuts (2^48) 3662151681 9 Manual.Count131072.C027910.packed 128 cuts27910 = true := by
 decide +kernel
def pointBounds27910 : List (Nat × Nat × Nat) := [(3662229504,104307697282033,104308080087666)]
theorem point_links_checked27910 : (cuts27910.take 1).map (fun c => (3662151681-1+2*2^9*c.k,104307422892873+c.lower,104307805698357+c.upper)) = pointBounds27910 := by
 decide +kernel
def cuts27911 : List PrefixCut := [⟨60,219888266,219888387⟩,
⟨128,459217084,459217341⟩]
theorem checked27911 : checkPrefixCuts (2^48) 3662282753 9 Manual.Count131072.C027911.packed 128 cuts27911 = true := by
 decide +kernel
def pointBounds27911 : List (Nat × Nat × Nat) := [(3662344192,104308097556796,104308480362653)]
theorem point_links_checked27911 : (cuts27911.take 1).map (fun c => (3662282753-1+2*2^9*c.k,104307877668530+c.lower,104308260474266+c.upper)) = pointBounds27911 := by
 decide +kernel
def cuts27912 : List PrefixCut := [⟨44,157013860,157013948⟩,
⟨128,460891355,460891608⟩]
theorem checked27912 : checkPrefixCuts (2^48) 3662413825 9 Manual.Count131072.C027912.packed 128 cuts27912 = true := by
 decide +kernel
def pointBounds27912 : List (Nat × Nat × Nat) := [(3662458880,104308493899474,104308876705555)]
theorem point_links_checked27912 : (cuts27912.take 1).map (fun c => (3662413825-1+2*2^9*c.k,104308336885614+c.lower,104308719691607+c.upper)) = pointBounds27912 := by
 decide +kernel
def cuts27913 : List PrefixCut := [⟨28,100445526,100445584⟩,
⟨128,456801726,456801984⟩]
theorem checked27913 : checkPrefixCuts (2^48) 3662544897 9 Manual.Count131072.C027913.packed 128 cuts27913 = true := by
 decide +kernel
def pointBounds27913 : List (Nat × Nat × Nat) := [(3662573568,104308898222495,104309281028799)]
theorem point_links_checked27913 : (cuts27913.take 1).map (fun c => (3662544897-1+2*2^9*c.k,104308797776969+c.lower,104309180583215+c.upper)) = pointBounds27913 := by
 decide +kernel
def cuts27914 : List PrefixCut := [⟨12,42344014,42344038⟩,
⟨124,443260306,443260559⟩,
⟨128,458399129,458399390⟩]
theorem checked27914 : checkPrefixCuts (2^48) 3662675969 9 Manual.Count131072.C027914.packed 128 cuts27914 = true := by
 decide +kernel
def pointBounds27914 : List (Nat × Nat × Nat) := [(3662688256,104309296922709,104309679729237),(3662802944,104309697839001,104310080645758)]
theorem point_links_checked27914 : (cuts27914.take 2).map (fun c => (3662675969-1+2*2^9*c.k,104309254578695+c.lower,104309637385199+c.upper)) = pointBounds27914 := by
 decide +kernel
def cuts27915 : List PrefixCut := [⟨108,387916600,387916814⟩,
⟨128,461610223,461610478⟩]
theorem checked27915 : checkPrefixCuts (2^48) 3662807041 9 Manual.Count131072.C027915.packed 128 cuts27915 = true := by
 decide +kernel
def pointBounds27915 : List (Nat × Nat × Nat) := [(3662917632,104310100894424,104310483701403)]
theorem point_links_checked27915 : (cuts27915.take 1).map (fun c => (3662807041-1+2*2^9*c.k,104309712977824+c.lower,104310095784589+c.upper)) = pointBounds27915 := by
 decide +kernel
def cuts27916 : List PrefixCut := [⟨92,328273433,328273617⟩,
⟨128,457674789,457675046⟩]
theorem checked27916 : checkPrefixCuts (2^48) 3662938113 9 Manual.Count131072.C027916.packed 128 cuts27916 = true := by
 decide +kernel
def pointBounds27916 : List (Nat × Nat × Nat) := [(3663032320,104310502861480,104310885668684)]
theorem point_links_checked27916 : (cuts27916.take 1).map (fun c => (3662938113-1+2*2^9*c.k,104310174588047+c.lower,104310557395067+c.upper)) = pointBounds27916 := by
 decide +kernel
def cuts27917 : List PrefixCut := [⟨76,270632096,270632248⟩,
⟨128,455737442,455737698⟩]
theorem checked27917 : checkPrefixCuts (2^48) 3663069185 9 Manual.Count131072.C027917.packed 128 cuts27917 = true := by
 decide +kernel
def pointBounds27917 : List (Nat × Nat × Nat) := [(3663147008,104310902894932,104311285702361)]
theorem point_links_checked27917 : (cuts27917.take 1).map (fun c => (3663069185-1+2*2^9*c.k,104310632262836+c.lower,104311015070113+c.upper)) = pointBounds27917 := by
 decide +kernel
def cuts27918 : List PrefixCut := [⟨60,214608193,214608311⟩,
⟨128,460177647,460177904⟩]
theorem checked27918 : checkPrefixCuts (2^48) 3663200257 9 Manual.Count131072.C027918.packed 128 cuts27918 = true := by
 decide +kernel
def pointBounds27918 : List (Nat × Nat × Nat) := [(3663261696,104311302608471,104311685416122)]
theorem point_links_checked27918 : (cuts27918.take 1).map (fun c => (3663200257-1+2*2^9*c.k,104311088000278+c.lower,104311470807811+c.upper)) = pointBounds27918 := by
 decide +kernel
def cuts27919 : List PrefixCut := [⟨44,156974516,156974604⟩,
⟨128,454552317,454552570⟩]
theorem checked27919 : checkPrefixCuts (2^48) 3663331329 9 Manual.Count131072.C027919.packed 128 cuts27919 = true := by
 decide +kernel
def pointBounds27919 : List (Nat × Nat × Nat) := [(3663376384,104311705152441,104312087960319)]
theorem point_links_checked27919 : (cuts27919.take 1).map (fun c => (3663331329-1+2*2^9*c.k,104311548177925+c.lower,104311930985715+c.upper)) = pointBounds27919 := by
 decide +kernel
def cuts27920 : List PrefixCut := [⟨28,97270229,97270285⟩,
⟨128,455534818,455535073⟩]
theorem checked27920 : checkPrefixCuts (2^48) 3663462401 9 Manual.Count131072.C027920.packed 128 cuts27920 = true := by
 decide +kernel
def pointBounds27920 : List (Nat × Nat × Nat) := [(3663491072,104312100000471,104312482808570)]
theorem point_links_checked27920 : (cuts27920.take 1).map (fun c => (3663462401-1+2*2^9*c.k,104312002730242+c.lower,104312385538285+c.upper)) = pointBounds27920 := by
 decide +kernel
def cuts27921 : List PrefixCut := [⟨12,42563903,42563927⟩,
⟨124,444224949,444225194⟩,
⟨128,457977085,457977337⟩]
theorem checked27921 : checkPrefixCuts (2^48) 3663593473 9 Manual.Count131072.C027921.packed 128 cuts27921 = true := by
 decide +kernel
def pointBounds27921 : List (Nat × Nat × Nat) := [(3663605760,104312500828963,104312883637285),(3663720448,104312902490009,104313285298552)]
theorem point_links_checked27921 : (cuts27921.take 2).map (fun c => (3663593473-1+2*2^9*c.k,104312458265060+c.lower,104312841073358+c.upper)) = pointBounds27921 := by
 decide +kernel
def cuts27922 : List PrefixCut := [⟨108,383517251,383517466⟩,
⟨128,455041320,455041573⟩]
theorem checked27922 : checkPrefixCuts (2^48) 3663724545 9 Manual.Count131072.C027922.packed 128 cuts27922 = true := by
 decide +kernel
def pointBounds27922 : List (Nat × Nat × Nat) := [(3663835136,104313299759396,104313682568161)]
theorem point_links_checked27922 : (cuts27922.take 1).map (fun c => (3663724545-1+2*2^9*c.k,104312916242145+c.lower,104313299050695+c.upper)) = pointBounds27922 := by
 decide +kernel
def cuts27923 : List PrefixCut := [⟨92,325425593,325425778⟩,
⟨128,451030252,451030509⟩]
theorem checked27923 : checkPrefixCuts (2^48) 3663855617 9 Manual.Count131072.C027923.packed 128 cuts27923 = true := by
 decide +kernel
def pointBounds27923 : List (Nat × Nat × Nat) := [(3663949824,104313696709058,104314079518046)]
theorem point_links_checked27923 : (cuts27923.take 1).map (fun c => (3663855617-1+2*2^9*c.k,104313371283465+c.lower,104313754092268+c.upper)) = pointBounds27923 := by
 decide +kernel
def cuts27924 : List PrefixCut := [⟨76,270871574,270871729⟩,
⟨128,463458901,463459163⟩]
theorem checked27924 : checkPrefixCuts (2^48) 3663986689 9 Manual.Count131072.C027924.packed 128 cuts27924 = true := by
 decide +kernel
def pointBounds27924 : List (Nat × Nat × Nat) := [(3664064512,104314093185291,104314475994506)]
theorem point_links_checked27924 : (cuts27924.take 1).map (fun c => (3663986689-1+2*2^9*c.k,104313822313717+c.lower,104314205122777+c.upper)) = pointBounds27924 := by
 decide +kernel
def cuts27925 : List PrefixCut := [⟨60,217473579,217473702⟩,
⟨128,454838931,454839188⟩]
theorem checked27925 : checkPrefixCuts (2^48) 3664117761 9 Manual.Count131072.C027925.packed 128 cuts27925 = true := by
 decide +kernel
def pointBounds27925 : List (Nat × Nat × Nat) := [(3664179200,104314503246197,104314886055642)]
theorem point_links_checked27925 : (cuts27925.take 1).map (fun c => (3664117761-1+2*2^9*c.k,104314285772618+c.lower,104314668581940+c.upper)) = pointBounds27925 := by
 decide +kernel
def cuts27926 : List PrefixCut := [⟨44,157549749,157549836⟩,
⟨128,456282014,456282266⟩]
theorem checked27926 : checkPrefixCuts (2^48) 3664248833 9 Manual.Count131072.C027926.packed 128 cuts27926 = true := by
 decide +kernel
def pointBounds27926 : List (Nat × Nat × Nat) := [(3664293888,104314898161298,104315280970964)]
theorem point_links_checked27926 : (cuts27926.take 1).map (fun c => (3664248833-1+2*2^9*c.k,104314740611549+c.lower,104315123421128+c.upper)) = pointBounds27926 := by
 decide +kernel
def cuts27927 : List PrefixCut := [⟨28,98474893,98474950⟩,
⟨128,456035231,456035488⟩]
theorem checked27927 : checkPrefixCuts (2^48) 3664379905 9 Manual.Count131072.C027927.packed 128 cuts27927 = true := by
 decide +kernel
def pointBounds27927 : List (Nat × Nat × Nat) := [(3664408576,104315295368456,104315678178344)]
theorem point_links_checked27927 : (cuts27927.take 1).map (fun c => (3664379905-1+2*2^9*c.k,104315196893563+c.lower,104315579703394+c.upper)) = pointBounds27927 := by
 decide +kernel
def cuts27928 : List PrefixCut := [⟨12,43014109,43014132⟩,
⟨124,450412084,450412329⟩,
⟨128,463930351,463930604⟩]
theorem checked27928 : checkPrefixCuts (2^48) 3664510977 9 Manual.Count131072.C027928.packed 128 cuts27928 = true := by
 decide +kernel
def pointBounds27928 : List (Nat × Nat × Nat) := [(3664523264,104315695942903,104316078753014),(3664637952,104316103340878,104316486151211)]
theorem point_links_checked27928 : (cuts27928.take 2).map (fun c => (3664510977-1+2*2^9*c.k,104315652928794+c.lower,104316035738882+c.upper)) = pointBounds27928 := by
 decide +kernel
def cuts27929 : List PrefixCut := [⟨108,384650077,384650291⟩,
⟨128,453160818,453161069⟩]
theorem checked27929 : checkPrefixCuts (2^48) 3664642049 9 Manual.Count131072.C027929.packed 128 cuts27929 = true := by
 decide +kernel
def pointBounds27929 : List (Nat × Nat × Nat) := [(3664752640,104316501509222,104316884319777)]
theorem point_links_checked27929 : (cuts27929.take 1).map (fun c => (3664642049-1+2*2^9*c.k,104316116859145+c.lower,104316499669486+c.upper)) = pointBounds27929 := by
 decide +kernel
def cuts27930 : List PrefixCut := [⟨92,326726626,326726814⟩,
⟨128,453451876,453452138⟩]
theorem checked27930 : checkPrefixCuts (2^48) 3664773121 9 Manual.Count131072.C027930.packed 128 cuts27930 = true := by
 decide +kernel
def pointBounds27930 : List (Nat × Nat × Nat) := [(3664867328,104316896746589,104317279557369)]
theorem point_links_checked27930 : (cuts27930.take 1).map (fun c => (3664773121-1+2*2^9*c.k,104316570019963+c.lower,104316952830555+c.upper)) = pointBounds27930 := by
 decide +kernel
def cuts27931 : List PrefixCut := [⟨76,270419793,270419940⟩,
⟨128,459272507,459272758⟩]
theorem checked27931 : checkPrefixCuts (2^48) 3664904193 9 Manual.Count131072.C027931.packed 128 cuts27931 = true := by
 decide +kernel
def pointBounds27931 : List (Nat × Nat × Nat) := [(3664982016,104317293891632,104317676702633)]
theorem point_links_checked27931 : (cuts27931.take 1).map (fun c => (3664904193-1+2*2^9*c.k,104317023471839+c.lower,104317406282693+c.upper)) = pointBounds27931 := by
 decide +kernel
def cuts27932 : List PrefixCut := [⟨60,213348753,213348871⟩,
⟨128,452267435,452267685⟩]
theorem checked27932 : checkPrefixCuts (2^48) 3665035265 9 Manual.Count131072.C027932.packed 128 cuts27932 = true := by
 decide +kernel
def pointBounds27932 : List (Nat × Nat × Nat) := [(3665096704,104317696093099,104318078904322)]
theorem point_links_checked27932 : (cuts27932.take 1).map (fun c => (3665035265-1+2*2^9*c.k,104317482744346+c.lower,104317865555451+c.upper)) = pointBounds27932 := by
 decide +kernel
def cuts27933 : List PrefixCut := [⟨44,154438450,154438538⟩,
⟨128,454708707,454708963⟩]
theorem checked27933 : checkPrefixCuts (2^48) 3665166337 9 Manual.Count131072.C027933.packed 128 cuts27933 = true := by
 decide +kernel
def pointBounds27933 : List (Nat × Nat × Nat) := [(3665211392,104318089450231,104318472261674)]
theorem point_links_checked27933 : (cuts27933.take 1).map (fun c => (3665166337-1+2*2^9*c.k,104317935011781+c.lower,104318317823136+c.upper)) = pointBounds27933 := by
 decide +kernel
def cuts27934 : List PrefixCut := [⟨28,100139709,100139766⟩,
⟨128,457764131,457764389⟩]
theorem checked27934 : checkPrefixCuts (2^48) 3665297409 9 Manual.Count131072.C027934.packed 128 cuts27934 = true := by
 decide +kernel
def pointBounds27934 : List (Nat × Nat × Nat) := [(3665326080,104318489860197,104318872671865)]
theorem point_links_checked27934 : (cuts27934.take 1).map (fun c => (3665297409-1+2*2^9*c.k,104318389720488+c.lower,104318772532099+c.upper)) = pointBounds27934 := by
 decide +kernel
def cuts27935 : List PrefixCut := [⟨12,42235425,42235450⟩,
⟨124,442773933,442774185⟩,
⟨128,457747809,457748070⟩]
theorem checked27935 : checkPrefixCuts (2^48) 3665428481 9 Manual.Count131072.C027935.packed 128 cuts27935 = true := by
 decide +kernel
def pointBounds27935 : List (Nat × Nat × Nat) := [(3665440768,104318889720044,104319272531938),(3665555456,104319290258552,104319673070673)]
theorem point_links_checked27935 : (cuts27935.take 2).map (fun c => (3665428481-1+2*2^9*c.k,104318847484619+c.lower,104319230296488+c.upper)) = pointBounds27935 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S3.B000247
