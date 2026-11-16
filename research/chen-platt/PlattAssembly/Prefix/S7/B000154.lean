import PlattAssemblyKernel
import PlattCertificates.Count131072.C064928
import PlattCertificates.Count131072.C064929
import PlattCertificates.Count131072.C064930
import PlattCertificates.Count131072.C064931
import PlattCertificates.Count131072.C064932
import PlattCertificates.Count131072.C064933
import PlattCertificates.Count131072.C064934
import PlattCertificates.Count131072.C064935
import PlattCertificates.Count131072.C064936
import PlattCertificates.Count131072.C064937
import PlattCertificates.Count131072.C064938
import PlattCertificates.Count131072.C064939
import PlattCertificates.Count131072.C064940
import PlattCertificates.Count131072.C064941
import PlattCertificates.Count131072.C064942
import PlattCertificates.Count131072.C064943
import PlattCertificates.Count131072.C064944
import PlattCertificates.Count131072.C064945
import PlattCertificates.Count131072.C064946
import PlattCertificates.Count131072.C064947
import PlattCertificates.Count131072.C064948
import PlattCertificates.Count131072.C064949
import PlattCertificates.Count131072.C064950
import PlattCertificates.Count131072.C064951
import PlattCertificates.Count131072.C064952
import PlattCertificates.Count131072.C064953
import PlattCertificates.Count131072.C064954
import PlattCertificates.Count131072.C064955
import PlattCertificates.Count131072.C064956
import PlattCertificates.Count131072.C064957
import PlattCertificates.Count131072.C064958
import PlattCertificates.Count131072.C064959
namespace ChenEffective.PlattWindow.Assembly.Prefix.S7.B000154
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts64928 : List PrefixCut := [⟨64,187743811,187743917⟩]
theorem checked64928 : checkPrefixCuts (2^48) 8514174977 10 Manual.Count131072.C064928.packed 64 cuts64928 = true := by
 decide +kernel
def cuts64929 : List PrefixCut := [⟨44,129326333,129326408⟩,
⟨64,187873154,187873264⟩]
theorem checked64929 : checkPrefixCuts (2^48) 8514306049 10 Manual.Count131072.C064929.packed 64 cuts64929 = true := by
 decide +kernel
def pointBounds64929 : List (Nat × Nat × Nat) := [(8514396160,114890084567709,114890473534044)]
theorem point_links_checked64929 : (cuts64929.take 1).map (fun c => (8514306049-1+2*2^10*c.k,114889955241376+c.lower,114890344207636+c.upper)) = pointBounds64929 := by
 decide +kernel
def cuts64930 : List PrefixCut := [⟨64,187209093,187209206⟩]
theorem checked64930 : checkPrefixCuts (2^48) 8514437121 10 Manual.Count131072.C064930.packed 64 cuts64930 = true := by
 decide +kernel
def cuts64931 : List PrefixCut := [⟨46,137917362,137917445⟩,
⟨64,192131819,192131936⟩]
theorem checked64931 : checkPrefixCuts (2^48) 8514568193 10 Manual.Count131072.C064931.packed 64 cuts64931 = true := by
 decide +kernel
def pointBounds64931 : List (Nat × Nat × Nat) := [(8514662400,114890468240985,114890857207551)]
theorem point_links_checked64931 : (cuts64931.take 1).map (fun c => (8514568193-1+2*2^10*c.k,114890330323623+c.lower,114890719290106+c.upper)) = pointBounds64931 := by
 decide +kernel
def cuts64932 : List PrefixCut := [⟨64,188889250,188889361⟩]
theorem checked64932 : checkPrefixCuts (2^48) 8514699265 10 Manual.Count131072.C064932.packed 64 cuts64932 = true := by
 decide +kernel
def cuts64933 : List PrefixCut := [⟨48,141185714,141185795⟩,
⟨64,188489668,188489777⟩]
theorem checked64933 : checkPrefixCuts (2^48) 8514830337 10 Manual.Count131072.C064933.packed 64 cuts64933 = true := by
 decide +kernel
def pointBounds64933 : List (Nat × Nat × Nat) := [(8514928640,114890852530406,114891241497198)]
theorem point_links_checked64933 : (cuts64933.take 1).map (fun c => (8514830337-1+2*2^10*c.k,114890711344692+c.lower,114891100311403+c.upper)) = pointBounds64933 := by
 decide +kernel
def cuts64934 : List PrefixCut := [⟨64,191990726,191990837⟩]
theorem checked64934 : checkPrefixCuts (2^48) 8514961409 10 Manual.Count131072.C064934.packed 64 cuts64934 = true := by
 decide +kernel
def cuts64935 : List PrefixCut := [⟨50,148222211,148222293⟩,
⟨64,189475534,189475639⟩]
theorem checked64935 : checkPrefixCuts (2^48) 8515092481 10 Manual.Count131072.C064935.packed 64 cuts64935 = true := by
 decide +kernel
def pointBounds64935 : List (Nat × Nat × Nat) := [(8515194880,114891240047297,114891629014310)]
theorem point_links_checked64935 : (cuts64935.take 1).map (fun c => (8515092481-1+2*2^10*c.k,114891091825086+c.lower,114891480792017+c.upper)) = pointBounds64935 := by
 decide +kernel
def cuts64936 : List PrefixCut := [⟨64,186629875,186629981⟩]
theorem checked64936 : checkPrefixCuts (2^48) 8515223553 10 Manual.Count131072.C064936.packed 64 cuts64936 = true := by
 decide +kernel
def cuts64937 : List PrefixCut := [⟨52,155126052,155126145⟩,
⟨64,192246279,192246392⟩]
theorem checked64937 : checkPrefixCuts (2^48) 8515354625 10 Manual.Count131072.C064937.packed 64 cuts64937 = true := by
 decide +kernel
def pointBounds64937 : List (Nat × Nat × Nat) := [(8515461120,114891623056547,114892012023782)]
theorem point_links_checked64937 : (cuts64937.take 1).map (fun c => (8515354625-1+2*2^10*c.k,114891467930495+c.lower,114891856897637+c.upper)) = pointBounds64937 := by
 decide +kernel
def cuts64938 : List PrefixCut := [⟨64,192573886,192573998⟩]
theorem checked64938 : checkPrefixCuts (2^48) 8515485697 10 Manual.Count131072.C064938.packed 64 cuts64938 = true := by
 decide +kernel
def cuts64939 : List PrefixCut := [⟨54,157897762,157897854⟩,
⟨64,186621251,186621360⟩]
theorem checked64939 : checkPrefixCuts (2^48) 8515616769 10 Manual.Count131072.C064939.packed 64 cuts64939 = true := by
 decide +kernel
def pointBounds64939 : List (Nat × Nat × Nat) := [(8515727360,114892010648422,114892399615881)]
theorem point_links_checked64939 : (cuts64939.take 1).map (fun c => (8515616769-1+2*2^10*c.k,114891852750660+c.lower,114892241718027+c.upper)) = pointBounds64939 := by
 decide +kernel
def cuts64940 : List PrefixCut := [⟨64,192700161,192700271⟩]
theorem checked64940 : checkPrefixCuts (2^48) 8515747841 10 Manual.Count131072.C064940.packed 64 cuts64940 = true := by
 decide +kernel
def cuts64941 : List PrefixCut := [⟨56,166949313,166949411⟩,
⟨64,191011512,191011623⟩]
theorem checked64941 : checkPrefixCuts (2^48) 8515878913 10 Manual.Count131072.C064941.packed 64 cuts64941 = true := by
 decide +kernel
def pointBounds64941 : List (Nat × Nat × Nat) := [(8515993600,114892399021385,114892787989069)]
theorem point_links_checked64941 : (cuts64941.take 1).map (fun c => (8515878913-1+2*2^10*c.k,114892232072072+c.lower,114892621039658+c.upper)) = pointBounds64941 := by
 decide +kernel
def cuts64942 : List PrefixCut := [⟨64,186810956,186811067⟩]
theorem checked64942 : checkPrefixCuts (2^48) 8516009985 10 Manual.Count131072.C064942.packed 64 cuts64942 = true := by
 decide +kernel
def cuts64943 : List PrefixCut := [⟨58,170117098,170117197⟩,
⟨64,188526753,188526863⟩]
theorem checked64943 : checkPrefixCuts (2^48) 8516141057 10 Manual.Count131072.C064943.packed 64 cuts64943 = true := by
 decide +kernel
def pointBounds64943 : List (Nat × Nat × Nat) := [(8516259840,114892780011638,114893168979545)]
theorem point_links_checked64943 : (cuts64943.take 1).map (fun c => (8516141057-1+2*2^10*c.k,114892609894540+c.lower,114892998862348+c.upper)) = pointBounds64943 := by
 decide +kernel
def cuts64944 : List PrefixCut := [⟨64,190804387,190804497⟩]
theorem checked64944 : checkPrefixCuts (2^48) 8516272129 10 Manual.Count131072.C064944.packed 64 cuts64944 = true := by
 decide +kernel
def cuts64945 : List PrefixCut := [⟨60,175829573,175829674⟩,
⟨64,188587036,188587143⟩]
theorem checked64945 : checkPrefixCuts (2^48) 8516403201 10 Manual.Count131072.C064945.packed 64 cuts64945 = true := by
 decide +kernel
def pointBounds64945 : List (Nat × Nat × Nat) := [(8516526080,114893165055253,114893554023382)]
theorem point_links_checked64945 : (cuts64945.take 1).map (fun c => (8516403201-1+2*2^10*c.k,114892989225680+c.lower,114893378193708+c.upper)) = pointBounds64945 := by
 decide +kernel
def cuts64946 : List PrefixCut := [⟨64,189013800,189013914⟩]
theorem checked64946 : checkPrefixCuts (2^48) 8516534273 10 Manual.Count131072.C064946.packed 64 cuts64946 = true := by
 decide +kernel
def cuts64947 : List PrefixCut := [⟨62,182566256,182566365⟩,
⟨64,189209185,189209297⟩]
theorem checked64947 : checkPrefixCuts (2^48) 8516665345 10 Manual.Count131072.C064947.packed 64 cuts64947 = true := by
 decide +kernel
def pointBounds64947 : List (Nat × Nat × Nat) := [(8516792320,114893549392772,114893938361130)]
theorem point_links_checked64947 : (cuts64947.take 1).map (fun c => (8516665345-1+2*2^10*c.k,114893366826516+c.lower,114893755794765+c.upper)) = pointBounds64947 := by
 decide +kernel
def cuts64948 : List PrefixCut := [⟨64,190726541,190726653⟩]
theorem checked64948 : checkPrefixCuts (2^48) 8516796417 10 Manual.Count131072.C064948.packed 64 cuts64948 = true := by
 decide +kernel
def cuts64949 : List PrefixCut := [⟨64,189269471,189269583⟩]
theorem checked64949 : checkPrefixCuts (2^48) 8516927489 10 Manual.Count131072.C064949.packed 64 cuts64949 = true := by
 decide +kernel
def pointBounds64949 : List (Nat × Nat × Nat) := [(8517058560,114893936031713,114894325000298)]
theorem point_links_checked64949 : (cuts64949.take 1).map (fun c => (8516927489-1+2*2^10*c.k,114893746762242+c.lower,114894135730715+c.upper)) = pointBounds64949 := by
 decide +kernel
def cuts64950 : List PrefixCut := [⟨64,190390189,190390300⟩]
theorem checked64950 : checkPrefixCuts (2^48) 8517058561 10 Manual.Count131072.C064950.packed 64 cuts64950 = true := by
 decide +kernel
def cuts64951 : List PrefixCut := [⟨64,191775267,191775382⟩]
theorem checked64951 : checkPrefixCuts (2^48) 8517189633 10 Manual.Count131072.C064951.packed 64 cuts64951 = true := by
 decide +kernel
def cuts64952 : List PrefixCut := [⟨2,5882427,5882431⟩,
⟨64,190615662,190615763⟩]
theorem checked64952 : checkPrefixCuts (2^48) 8517320705 10 Manual.Count131072.C064952.packed 64 cuts64952 = true := by
 decide +kernel
def pointBounds64952 : List (Nat × Nat × Nat) := [(8517324800,114894324079596,114894713048411)]
theorem point_links_checked64952 : (cuts64952.take 1).map (fun c => (8517320705-1+2*2^10*c.k,114894318197169+c.lower,114894707165980+c.upper)) = pointBounds64952 := by
 decide +kernel
def cuts64953 : List PrefixCut := [⟨64,190150091,190150197⟩]
theorem checked64953 : checkPrefixCuts (2^48) 8517451777 10 Manual.Count131072.C064953.packed 64 cuts64953 = true := by
 decide +kernel
def cuts64954 : List PrefixCut := [⟨4,11863628,11863635⟩,
⟨64,188891392,188891502⟩]
theorem checked64954 : checkPrefixCuts (2^48) 8517582849 10 Manual.Count131072.C064954.packed 64 cuts64954 = true := by
 decide +kernel
def pointBounds64954 : List (Nat × Nat × Nat) := [(8517591040,114894710826550,114895099795575)]
theorem point_links_checked64954 : (cuts64954.take 1).map (fun c => (8517582849-1+2*2^10*c.k,114894698962922+c.lower,114895087931940+c.upper)) = pointBounds64954 := by
 decide +kernel
def cuts64955 : List PrefixCut := [⟨64,191102546,191102661⟩]
theorem checked64955 : checkPrefixCuts (2^48) 8517713921 10 Manual.Count131072.C064955.packed 64 cuts64955 = true := by
 decide +kernel
def cuts64956 : List PrefixCut := [⟨6,17910550,17910560⟩,
⟨64,189447352,189447466⟩]
theorem checked64956 : checkPrefixCuts (2^48) 8517844993 10 Manual.Count131072.C064956.packed 64 cuts64956 = true := by
 decide +kernel
def pointBounds64956 : List (Nat × Nat × Nat) := [(8517857280,114895096867410,114895485836663)]
theorem point_links_checked64956 : (cuts64956.take 1).map (fun c => (8517844993-1+2*2^10*c.k,114895078956860+c.lower,114895467926103+c.upper)) = pointBounds64956 := by
 decide +kernel
def cuts64957 : List PrefixCut := [⟨64,190336632,190336744⟩]
theorem checked64957 : checkPrefixCuts (2^48) 8517976065 10 Manual.Count131072.C064957.packed 64 cuts64957 = true := by
 decide +kernel
def cuts64958 : List PrefixCut := [⟨8,23362300,23362312⟩,
⟨64,187359744,187359850⟩]
theorem checked64958 : checkPrefixCuts (2^48) 8518107137 10 Manual.Count131072.C064958.packed 64 cuts64958 = true := by
 decide +kernel
def pointBounds64958 : List (Nat × Nat × Nat) := [(8518123520,114895482103144,114895871072625)]
theorem point_links_checked64958 : (cuts64958.take 1).map (fun c => (8518107137-1+2*2^10*c.k,114895458740844+c.lower,114895847710313+c.upper)) = pointBounds64958 := by
 decide +kernel
def cuts64959 : List PrefixCut := [⟨64,189405571,189405677⟩]
theorem checked64959 : checkPrefixCuts (2^48) 8518238209 10 Manual.Count131072.C064959.packed 64 cuts64959 = true := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S7.B000154
