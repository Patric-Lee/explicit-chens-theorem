import PlattAssemblyKernel
import PlattCertificates.Count131072.C044928
import PlattCertificates.Count131072.C044929
import PlattCertificates.Count131072.C044930
import PlattCertificates.Count131072.C044931
import PlattCertificates.Count131072.C044932
import PlattCertificates.Count131072.C044933
import PlattCertificates.Count131072.C044934
import PlattCertificates.Count131072.C044935
import PlattCertificates.Count131072.C044936
import PlattCertificates.Count131072.C044937
import PlattCertificates.Count131072.C044938
import PlattCertificates.Count131072.C044939
import PlattCertificates.Count131072.C044940
import PlattCertificates.Count131072.C044941
import PlattCertificates.Count131072.C044942
import PlattCertificates.Count131072.C044943
import PlattCertificates.Count131072.C044944
import PlattCertificates.Count131072.C044945
import PlattCertificates.Count131072.C044946
import PlattCertificates.Count131072.C044947
import PlattCertificates.Count131072.C044948
import PlattCertificates.Count131072.C044949
import PlattCertificates.Count131072.C044950
import PlattCertificates.Count131072.C044951
import PlattCertificates.Count131072.C044952
import PlattCertificates.Count131072.C044953
import PlattCertificates.Count131072.C044954
import PlattCertificates.Count131072.C044955
import PlattCertificates.Count131072.C044956
import PlattCertificates.Count131072.C044957
import PlattCertificates.Count131072.C044958
import PlattCertificates.Count131072.C044959
namespace ChenEffective.PlattWindow.Assembly.Prefix.S5.B000154
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts44928 : List PrefixCut := [⟨64,276182417,276182574⟩]
theorem checked44928 : checkPrefixCuts (2^48) 5892734977 10 Manual.Count131072.C044928.packed 64 cuts44928 = true := by
 decide +kernel
def cuts44929 : List PrefixCut := [⟨17,76185530,76185577⟩,
⟨64,280713945,280714112⟩]
theorem checked44929 : checkPrefixCuts (2^48) 5892866049 10 Manual.Count131072.C044929.packed 64 cuts44929 = true := by
 decide +kernel
def pointBounds44929 : List (Nat × Nat × Nat) := [(5892900864,110322951953775,110323338311786)]
theorem point_links_checked44929 : (cuts44929.take 1).map (fun c => (5892866049-1+2*2^10*c.k,110322875768245+c.lower,110323262126209+c.upper)) = pointBounds44929 := by
 decide +kernel
def cuts44930 : List PrefixCut := [⟨43,185753988,185754095⟩,
⟨64,277364213,277364375⟩]
theorem checked44930 : checkPrefixCuts (2^48) 5892997121 10 Manual.Count131072.C044930.packed 64 cuts44930 = true := by
 decide +kernel
def pointBounds44930 : List (Nat × Nat × Nat) := [(5893085184,110323342236178,110323728594416)]
theorem point_links_checked44930 : (cuts44930.take 1).map (fun c => (5892997121-1+2*2^10*c.k,110323156482190+c.lower,110323542840321+c.upper)) = pointBounds44930 := by
 decide +kernel
def cuts44931 : List PrefixCut := [⟨64,279125272,279125425⟩]
theorem checked44931 : checkPrefixCuts (2^48) 5893128193 10 Manual.Count131072.C044931.packed 64 cuts44931 = true := by
 decide +kernel
def cuts44932 : List PrefixCut := [⟨5,22352679,22352693⟩,
⟨64,277017568,277017731⟩]
theorem checked44932 : checkPrefixCuts (2^48) 5893259265 10 Manual.Count131072.C044932.packed 64 cuts44932 = true := by
 decide +kernel
def pointBounds44932 : List (Nat × Nat × Nat) := [(5893269504,110323735324354,110324121682814)]
theorem point_links_checked44932 : (cuts44932.take 1).map (fun c => (5893259265-1+2*2^10*c.k,110323712971675+c.lower,110324099330121+c.upper)) = pointBounds44932 := by
 decide +kernel
def cuts44933 : List PrefixCut := [⟨31,137169193,137169271⟩,
⟨64,278730796,278730954⟩]
theorem checked44933 : checkPrefixCuts (2^48) 5893390337 10 Manual.Count131072.C044933.packed 64 cuts44933 = true := by
 decide +kernel
def pointBounds44933 : List (Nat × Nat × Nat) := [(5893453824,110324127158436,110324513517123)]
theorem point_links_checked44933 : (cuts44933.take 1).map (fun c => (5893390337-1+2*2^10*c.k,110323989989243+c.lower,110324376347852+c.upper)) = pointBounds44933 := by
 decide +kernel
def cuts44934 : List PrefixCut := [⟨57,244720100,244720250⟩,
⟨64,274712784,274712949⟩]
theorem checked44934 : checkPrefixCuts (2^48) 5893521409 10 Manual.Count131072.C044934.packed 64 cuts44934 = true := by
 decide +kernel
def pointBounds44934 : List (Nat × Nat × Nat) := [(5893638144,110324513440139,110324899799056)]
theorem point_links_checked44934 : (cuts44934.take 1).map (fun c => (5893521409-1+2*2^10*c.k,110324268720039+c.lower,110324655078806+c.upper)) = pointBounds44934 := by
 decide +kernel
def cuts44935 : List PrefixCut := [⟨64,278479589,278479752⟩]
theorem checked44935 : checkPrefixCuts (2^48) 5893652481 10 Manual.Count131072.C044935.packed 64 cuts44935 = true := by
 decide +kernel
def cuts44936 : List PrefixCut := [⟨19,82429914,82429958⟩,
⟨64,280574709,280574861⟩]
theorem checked44936 : checkPrefixCuts (2^48) 5893783553 10 Manual.Count131072.C044936.packed 64 cuts44936 = true := by
 decide +kernel
def pointBounds44936 : List (Nat × Nat × Nat) := [(5893822464,110324904342326,110325290701465)]
theorem point_links_checked44936 : (cuts44936.take 1).map (fun c => (5893783553-1+2*2^10*c.k,110324821912412+c.lower,110325208271507+c.upper)) = pointBounds44936 := by
 decide +kernel
def cuts44937 : List PrefixCut := [⟨45,197186557,197186670⟩,
⟨64,278562717,278562876⟩]
theorem checked44937 : checkPrefixCuts (2^48) 5893914625 10 Manual.Count131072.C044937.packed 64 cuts44937 = true := by
 decide +kernel
def pointBounds44937 : List (Nat × Nat × Nat) := [(5894006784,110325299673678,110325686033038)]
theorem point_links_checked44937 : (cuts44937.take 1).map (fun c => (5893914625-1+2*2^10*c.k,110325102487121+c.lower,110325488846368+c.upper)) = pointBounds44937 := by
 decide +kernel
def cuts44938 : List PrefixCut := [⟨64,275547945,275548102⟩]
theorem checked44938 : checkPrefixCuts (2^48) 5894045697 10 Manual.Count131072.C044938.packed 64 cuts44938 = true := by
 decide +kernel
def cuts44939 : List PrefixCut := [⟨7,30992789,30992806⟩,
⟨64,280173975,280174134⟩]
theorem checked44939 : checkPrefixCuts (2^48) 5894176769 10 Manual.Count131072.C044939.packed 64 cuts44939 = true := by
 decide +kernel
def pointBounds44939 : List (Nat × Nat × Nat) := [(5894191104,110325687590572,110326073950152)]
theorem point_links_checked44939 : (cuts44939.take 1).map (fun c => (5894176769-1+2*2^10*c.k,110325656597783+c.lower,110326042957346+c.upper)) = pointBounds44939 := by
 decide +kernel
def cuts44940 : List PrefixCut := [⟨33,143403482,143403568⟩,
⟨64,276681757,276681924⟩]
theorem checked44940 : checkPrefixCuts (2^48) 5894307841 10 Manual.Count131072.C044940.packed 64 cuts44940 = true := by
 decide +kernel
def pointBounds44940 : List (Nat × Nat × Nat) := [(5894375424,110326080175240,110326466535048)]
theorem point_links_checked44940 : (cuts44940.take 1).map (fun c => (5894307841-1+2*2^10*c.k,110325936771758+c.lower,110326323131480+c.upper)) = pointBounds44940 := by
 decide +kernel
def cuts44941 : List PrefixCut := [⟨59,257145191,257145337⟩,
⟨64,278633412,278633569⟩]
theorem checked44941 : checkPrefixCuts (2^48) 5894438913 10 Manual.Count131072.C044941.packed 64 cuts44941 = true := by
 decide +kernel
def pointBounds44941 : List (Nat × Nat × Nat) := [(5894559744,110326470598706,110326856958741)]
theorem point_links_checked44941 : (cuts44941.take 1).map (fun c => (5894438913-1+2*2^10*c.k,110326213453515+c.lower,110326599813404+c.upper)) = pointBounds44941 := by
 decide +kernel
def cuts44942 : List PrefixCut := [⟨64,280680527,280680688⟩]
theorem checked44942 : checkPrefixCuts (2^48) 5894569985 10 Manual.Count131072.C044942.packed 64 cuts44942 = true := by
 decide +kernel
def cuts44943 : List PrefixCut := [⟨21,90486860,90486913⟩,
⟨64,275803784,275803945⟩]
theorem checked44943 : checkPrefixCuts (2^48) 5894701057 10 Manual.Count131072.C044943.packed 64 cuts44943 = true := by
 decide +kernel
def pointBounds44943 : List (Nat × Nat × Nat) := [(5894744064,110326863254314,110327249614574)]
theorem point_links_checked44943 : (cuts44943.take 1).map (fun c => (5894701057-1+2*2^10*c.k,110326772767454+c.lower,110327159127661+c.upper)) = pointBounds44943 := by
 decide +kernel
def cuts44944 : List PrefixCut := [⟨47,205798385,205798502⟩,
⟨64,281909516,281909675⟩]
theorem checked44944 : checkPrefixCuts (2^48) 5894832129 10 Manual.Count131072.C044944.packed 64 cuts44944 = true := by
 decide +kernel
def pointBounds44944 : List (Nat × Nat × Nat) := [(5894928384,110327254369623,110327640730108)]
theorem point_links_checked44944 : (cuts44944.take 1).map (fun c => (5894832129-1+2*2^10*c.k,110327048571238+c.lower,110327434931606+c.upper)) = pointBounds44944 := by
 decide +kernel
def cuts44945 : List PrefixCut := [⟨64,276459996,276460160⟩]
theorem checked44945 : checkPrefixCuts (2^48) 5894963201 10 Manual.Count131072.C044945.packed 64 cuts44945 = true := by
 decide +kernel
def cuts44946 : List PrefixCut := [⟨9,38866250,38866273⟩,
⟨64,278172717,278172882⟩]
theorem checked44946 : checkPrefixCuts (2^48) 5895094273 10 Manual.Count131072.C044946.packed 64 cuts44946 = true := by
 decide +kernel
def pointBounds44946 : List (Nat × Nat × Nat) := [(5895112704,110327645807000,110328032167714)]
theorem point_links_checked44946 : (cuts44946.take 1).map (fun c => (5895094273-1+2*2^10*c.k,110327606940750+c.lower,110327993301441+c.upper)) = pointBounds44946 := by
 decide +kernel
def cuts44947 : List PrefixCut := [⟨35,152548347,152548434⟩,
⟨64,279551187,279551347⟩]
theorem checked44947 : checkPrefixCuts (2^48) 5895225345 10 Manual.Count131072.C044947.packed 64 cuts44947 = true := by
 decide +kernel
def pointBounds44947 : List (Nat × Nat × Nat) := [(5895297024,110328037661814,110328424022757)]
theorem point_links_checked44947 : (cuts44947.take 1).map (fun c => (5895225345-1+2*2^10*c.k,110327885113467+c.lower,110328271474323+c.upper)) = pointBounds44947 := by
 decide +kernel
def cuts44948 : List PrefixCut := [⟨61,263168712,263168861⟩,
⟨64,275725423,275725581⟩]
theorem checked44948 : checkPrefixCuts (2^48) 5895356417 10 Manual.Count131072.C044948.packed 64 cuts44948 = true := by
 decide +kernel
def pointBounds44948 : List (Nat × Nat × Nat) := [(5895481344,110328427833366,110328814194531)]
theorem point_links_checked44948 : (cuts44948.take 1).map (fun c => (5895356417-1+2*2^10*c.k,110328164664654+c.lower,110328551025670+c.upper)) = pointBounds44948 := by
 decide +kernel
def cuts44949 : List PrefixCut := [⟨64,281257543,281257702⟩]
theorem checked44949 : checkPrefixCuts (2^48) 5895487489 10 Manual.Count131072.C044949.packed 64 cuts44949 = true := by
 decide +kernel
def cuts44950 : List PrefixCut := [⟨23,99925834,99925893⟩,
⟨64,278291230,278291392⟩]
theorem checked44950 : checkPrefixCuts (2^48) 5895618561 10 Manual.Count131072.C044950.packed 64 cuts44950 = true := by
 decide +kernel
def pointBounds44950 : List (Nat × Nat × Nat) := [(5895665664,110328821573454,110329207934846)]
theorem point_links_checked44950 : (cuts44950.take 1).map (fun c => (5895618561-1+2*2^10*c.k,110328721647620+c.lower,110329108008953+c.upper)) = pointBounds44950 := by
 decide +kernel
def cuts44951 : List PrefixCut := [⟨49,210683660,210683781⟩,
⟨64,274704428,274704585⟩]
theorem checked44951 : checkPrefixCuts (2^48) 5895749633 10 Manual.Count131072.C044951.packed 64 cuts44951 = true := by
 decide +kernel
def pointBounds44951 : List (Nat × Nat × Nat) := [(5895849984,110329210622510,110329596984126)]
theorem point_links_checked44951 : (cuts44951.take 1).map (fun c => (5895749633-1+2*2^10*c.k,110328999938850+c.lower,110329386300345+c.upper)) = pointBounds44951 := by
 decide +kernel
def cuts44952 : List PrefixCut := [⟨64,274889291,274889442⟩]
theorem checked44952 : checkPrefixCuts (2^48) 5895880705 10 Manual.Count131072.C044952.packed 64 cuts44952 = true := by
 decide +kernel
def cuts44953 : List PrefixCut := [⟨11,48121707,48121738⟩,
⟨64,280420931,280421098⟩]
theorem checked44953 : checkPrefixCuts (2^48) 5896011777 10 Manual.Count131072.C044953.packed 64 cuts44953 = true := by
 decide +kernel
def pointBounds44953 : List (Nat × Nat × Nat) := [(5896034304,110329597654276,110329984016110)]
theorem point_links_checked44953 : (cuts44953.take 1).map (fun c => (5896011777-1+2*2^10*c.k,110329549532569+c.lower,110329935894372+c.upper)) = pointBounds44953 := by
 decide +kernel
def cuts44954 : List PrefixCut := [⟨37,161403903,161403997⟩,
⟨64,277884572,277884733⟩]
theorem checked44954 : checkPrefixCuts (2^48) 5896142849 10 Manual.Count131072.C044954.packed 64 cuts44954 = true := by
 decide +kernel
def pointBounds44954 : List (Nat × Nat × Nat) := [(5896218624,110329991357403,110330377719467)]
theorem point_links_checked44954 : (cuts44954.take 1).map (fun c => (5896142849-1+2*2^10*c.k,110329829953500+c.lower,110330216315470+c.upper)) = pointBounds44954 := by
 decide +kernel
def cuts44955 : List PrefixCut := [⟨63,274107211,274107364⟩,
⟨64,278403514,278403670⟩]
theorem checked44955 : checkPrefixCuts (2^48) 5896273921 10 Manual.Count131072.C044955.packed 64 cuts44955 = true := by
 decide +kernel
def pointBounds44955 : List (Nat × Nat × Nat) := [(5896402944,110330381945283,110330768307567)]
theorem point_links_checked44955 : (cuts44955.take 1).map (fun c => (5896273921-1+2*2^10*c.k,110330107838072+c.lower,110330494200203+c.upper)) = pointBounds44955 := by
 decide +kernel
def cuts44956 : List PrefixCut := [⟨64,279829389,279829551⟩]
theorem checked44956 : checkPrefixCuts (2^48) 5896404993 10 Manual.Count131072.C044956.packed 64 cuts44956 = true := by
 decide +kernel
def cuts44957 : List PrefixCut := [⟨25,107595650,107595711⟩,
⟨64,275336076,275336233⟩]
theorem checked44957 : checkPrefixCuts (2^48) 5896536065 10 Manual.Count131072.C044957.packed 64 cuts44957 = true := by
 decide +kernel
def pointBounds44957 : List (Nat × Nat × Nat) := [(5896587264,110330773666625,110331160029135)]
theorem point_links_checked44957 : (cuts44957.take 1).map (fun c => (5896536065-1+2*2^10*c.k,110330666070975+c.lower,110331052433424+c.upper)) = pointBounds44957 := by
 decide +kernel
def cuts44958 : List PrefixCut := [⟨51,225687074,225687210⟩,
⟨64,280007935,280008105⟩]
theorem checked44958 : checkPrefixCuts (2^48) 5896667137 10 Manual.Count131072.C044958.packed 64 cuts44958 = true := by
 decide +kernel
def pointBounds44958 : List (Nat × Nat × Nat) := [(5896771584,110331167094125,110331553456867)]
theorem point_links_checked44958 : (cuts44958.take 1).map (fun c => (5896667137-1+2*2^10*c.k,110330941407051+c.lower,110331327769657+c.upper)) = pointBounds44958 := by
 decide +kernel
def cuts44959 : List PrefixCut := [⟨64,277137644,277137810⟩]
theorem checked44959 : checkPrefixCuts (2^48) 5896798209 10 Manual.Count131072.C044959.packed 64 cuts44959 = true := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S5.B000154
