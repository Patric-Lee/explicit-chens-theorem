import PlattAssemblyKernel
import PlattCertificates.Count131072.C061920
import PlattCertificates.Count131072.C061921
import PlattCertificates.Count131072.C061922
import PlattCertificates.Count131072.C061923
import PlattCertificates.Count131072.C061924
import PlattCertificates.Count131072.C061925
import PlattCertificates.Count131072.C061926
import PlattCertificates.Count131072.C061927
import PlattCertificates.Count131072.C061928
import PlattCertificates.Count131072.C061929
import PlattCertificates.Count131072.C061930
import PlattCertificates.Count131072.C061931
import PlattCertificates.Count131072.C061932
import PlattCertificates.Count131072.C061933
import PlattCertificates.Count131072.C061934
import PlattCertificates.Count131072.C061935
import PlattCertificates.Count131072.C061936
import PlattCertificates.Count131072.C061937
import PlattCertificates.Count131072.C061938
import PlattCertificates.Count131072.C061939
import PlattCertificates.Count131072.C061940
import PlattCertificates.Count131072.C061941
import PlattCertificates.Count131072.C061942
import PlattCertificates.Count131072.C061943
import PlattCertificates.Count131072.C061944
import PlattCertificates.Count131072.C061945
import PlattCertificates.Count131072.C061946
import PlattCertificates.Count131072.C061947
import PlattCertificates.Count131072.C061948
import PlattCertificates.Count131072.C061949
import PlattCertificates.Count131072.C061950
import PlattCertificates.Count131072.C061951
namespace ChenEffective.PlattWindow.Assembly.Prefix.S7.B000060
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts61920 : List PrefixCut := [⟨16,49986508,49986538⟩,
⟨64,199979493,199979609⟩]
theorem checked61920 : checkPrefixCuts (2^48) 8119910401 10 Manual.Count131072.C061920.packed 64 cuts61920 = true := by
 decide +kernel
def pointBounds61920 : List (Nat × Nat × Nat) := [(8119943168,114305527848280,114305916477947)]
theorem point_links_checked61920 : (cuts61920.take 1).map (fun c => (8119910401-1+2*2^10*c.k,114305477861772+c.lower,114305866491409+c.upper)) = pointBounds61920 := by
 decide +kernel
def cuts61921 : List PrefixCut := [⟨64,199317621,199317732⟩]
theorem checked61921 : checkPrefixCuts (2^48) 8120041473 10 Manual.Count131072.C061921.packed 64 cuts61921 = true := by
 decide +kernel
def cuts61922 : List PrefixCut := [⟨12,35946161,35946182⟩,
⟨64,196714674,196714786⟩]
theorem checked61922 : checkPrefixCuts (2^48) 8120172545 10 Manual.Count131072.C061922.packed 64 cuts61922 = true := by
 decide +kernel
def pointBounds61922 : List (Nat × Nat × Nat) := [(8120197120,114305913105047,114306301734932)]
theorem point_links_checked61922 : (cuts61922.take 1).map (fun c => (8120172545-1+2*2^10*c.k,114305877158886+c.lower,114306265788750+c.upper)) = pointBounds61922 := by
 decide +kernel
def cuts61923 : List PrefixCut := [⟨64,200697728,200697846⟩]
theorem checked61923 : checkPrefixCuts (2^48) 8120303617 10 Manual.Count131072.C061923.packed 64 cuts61923 = true := by
 decide +kernel
def cuts61924 : List PrefixCut := [⟨8,24263754,24263767⟩,
⟨64,197436247,197436358⟩]
theorem checked61924 : checkPrefixCuts (2^48) 8120434689 10 Manual.Count131072.C061924.packed 64 cuts61924 = true := by
 decide +kernel
def pointBounds61924 : List (Nat × Nat × Nat) := [(8120451072,114306298835042,114306687465149)]
theorem point_links_checked61924 : (cuts61924.take 1).map (fun c => (8120434689-1+2*2^10*c.k,114306274571288+c.lower,114306663201382+c.upper)) = pointBounds61924 := by
 decide +kernel
def cuts61925 : List PrefixCut := [⟨64,198888848,198888959⟩]
theorem checked61925 : checkPrefixCuts (2^48) 8120565761 10 Manual.Count131072.C061925.packed 64 cuts61925 = true := by
 decide +kernel
def cuts61926 : List PrefixCut := [⟨4,12443443,12443451⟩,
⟨64,193721110,193721218⟩]
theorem checked61926 : checkPrefixCuts (2^48) 8120696833 10 Manual.Count131072.C061926.packed 64 cuts61926 = true := by
 decide +kernel
def pointBounds61926 : List (Nat × Nat × Nat) := [(8120705024,114306683339826,114307071970150)]
theorem point_links_checked61926 : (cuts61926.take 1).map (fun c => (8120696833-1+2*2^10*c.k,114306670896383+c.lower,114307059526699+c.upper)) = pointBounds61926 := by
 decide +kernel
def cuts61927 : List PrefixCut := [⟨64,200684776,200684889⟩]
theorem checked61927 : checkPrefixCuts (2^48) 8120827905 10 Manual.Count131072.C061927.packed 64 cuts61927 = true := by
 decide +kernel
def pointBounds61927 : List (Nat × Nat × Nat) := [(8120958976,114307065302269,114307453932806)]
theorem point_links_checked61927 : (cuts61927.take 1).map (fun c => (8120827905-1+2*2^10*c.k,114306864617493+c.lower,114307253247917+c.upper)) = pointBounds61927 := by
 decide +kernel
def cuts61928 : List PrefixCut := [⟨64,199676397,199676511⟩]
theorem checked61928 : checkPrefixCuts (2^48) 8120958977 10 Manual.Count131072.C061928.packed 64 cuts61928 = true := by
 decide +kernel
def cuts61929 : List PrefixCut := [⟨60,184457742,184457851⟩,
⟨64,196935055,196935171⟩]
theorem checked61929 : checkPrefixCuts (2^48) 8121090049 10 Manual.Count131072.C061929.packed 64 cuts61929 = true := by
 decide +kernel
def pointBounds61929 : List (Nat × Nat × Nat) := [(8121212928,114307449436408,114307838067168)]
theorem point_links_checked61929 : (cuts61929.take 1).map (fun c => (8121090049-1+2*2^10*c.k,114307264978666+c.lower,114307653609317+c.upper)) = pointBounds61929 := by
 decide +kernel
def cuts61930 : List PrefixCut := [⟨64,199254053,199254169⟩]
theorem checked61930 : checkPrefixCuts (2^48) 8121221121 10 Manual.Count131072.C061930.packed 64 cuts61930 = true := by
 decide +kernel
def cuts61931 : List PrefixCut := [⟨56,175232773,175232875⟩,
⟨64,199632075,199632192⟩]
theorem checked61931 : checkPrefixCuts (2^48) 8121352193 10 Manual.Count131072.C061931.packed 64 cuts61931 = true := by
 decide +kernel
def pointBounds61931 : List (Nat × Nat × Nat) := [(8121466880,114307836400547,114308225031532)]
theorem point_links_checked61931 : (cuts61931.take 1).map (fun c => (8121352193-1+2*2^10*c.k,114307661167774+c.lower,114308049798657+c.upper)) = pointBounds61931 := by
 decide +kernel
def cuts61932 : List PrefixCut := [⟨64,200772555,200772675⟩]
theorem checked61932 : checkPrefixCuts (2^48) 8121483265 10 Manual.Count131072.C061932.packed 64 cuts61932 = true := by
 decide +kernel
def cuts61933 : List PrefixCut := [⟨52,161918811,161918903⟩,
⟨64,199279056,199279171⟩]
theorem checked61933 : checkPrefixCuts (2^48) 8121614337 10 Manual.Count131072.C061933.packed 64 cuts61933 = true := by
 decide +kernel
def pointBounds61933 : List (Nat × Nat × Nat) := [(8121720832,114308223491215,114308612122427)]
theorem point_links_checked61933 : (cuts61933.take 1).map (fun c => (8121614337-1+2*2^10*c.k,114308061572404+c.lower,114308450203524+c.upper)) = pointBounds61933 := by
 decide +kernel
def cuts61934 : List PrefixCut := [⟨64,198236131,198236247⟩]
theorem checked61934 : checkPrefixCuts (2^48) 8121745409 10 Manual.Count131072.C061934.packed 64 cuts61934 = true := by
 decide +kernel
def cuts61935 : List PrefixCut := [⟨48,150234538,150234624⟩,
⟨64,199064700,199064812⟩]
theorem checked61935 : checkPrefixCuts (2^48) 8121876481 10 Manual.Count131072.C061935.packed 64 cuts61935 = true := by
 decide +kernel
def pointBounds61935 : List (Nat × Nat × Nat) := [(8121974784,114308609322129,114308997953566)]
theorem point_links_checked61935 : (cuts61935.take 1).map (fun c => (8121876481-1+2*2^10*c.k,114308459087591+c.lower,114308847718942+c.upper)) = pointBounds61935 := by
 decide +kernel
def cuts61936 : List PrefixCut := [⟨64,201210100,201210217⟩]
theorem checked61936 : checkPrefixCuts (2^48) 8122007553 10 Manual.Count131072.C061936.packed 64 cuts61936 = true := by
 decide +kernel
def cuts61937 : List PrefixCut := [⟨44,134531011,134531088⟩,
⟨64,193166924,193167035⟩]
theorem checked61937 : checkPrefixCuts (2^48) 8122138625 10 Manual.Count131072.C061937.packed 64 cuts61937 = true := by
 decide +kernel
def pointBounds61937 : List (Nat × Nat × Nat) := [(8122228736,114308993893402,114309382525059)]
theorem point_links_checked61937 : (cuts61937.take 1).map (fun c => (8122138625-1+2*2^10*c.k,114308859362391+c.lower,114309247993971+c.upper)) = pointBounds61937 := by
 decide +kernel
def cuts61938 : List PrefixCut := [⟨64,201065005,201065125⟩]
theorem checked61938 : checkPrefixCuts (2^48) 8122269697 10 Manual.Count131072.C061938.packed 64 cuts61938 = true := by
 decide +kernel
def cuts61939 : List PrefixCut := [⟨40,124892923,124892996⟩,
⟨64,200195401,200195515⟩]
theorem checked61939 : checkPrefixCuts (2^48) 8122400769 10 Manual.Count131072.C061939.packed 64 cuts61939 = true := by
 decide +kernel
def pointBounds61939 : List (Nat × Nat × Nat) := [(8122482688,114309378487243,114309767119127)]
theorem point_links_checked61939 : (cuts61939.take 1).map (fun c => (8122400769-1+2*2^10*c.k,114309253594320+c.lower,114309642226131+c.upper)) = pointBounds61939 := by
 decide +kernel
def cuts61940 : List PrefixCut := [⟨64,195444672,195444788⟩]
theorem checked61940 : checkPrefixCuts (2^48) 8122531841 10 Manual.Count131072.C061940.packed 64 cuts61940 = true := by
 decide +kernel
def cuts61941 : List PrefixCut := [⟨36,110785243,110785304⟩,
⟨64,199703804,199703914⟩]
theorem checked61941 : checkPrefixCuts (2^48) 8122662913 10 Manual.Count131072.C061941.packed 64 cuts61941 = true := by
 decide +kernel
def pointBounds61941 : List (Nat × Nat × Nat) := [(8122736640,114309760019636,114310148651738)]
theorem point_links_checked61941 : (cuts61941.take 1).map (fun c => (8122662913-1+2*2^10*c.k,114309649234393+c.lower,114310037866434+c.upper)) = pointBounds61941 := by
 decide +kernel
def cuts61942 : List PrefixCut := [⟨64,202195559,202195674⟩]
theorem checked61942 : checkPrefixCuts (2^48) 8122793985 10 Manual.Count131072.C061942.packed 64 cuts61942 = true := by
 decide +kernel
def cuts61943 : List PrefixCut := [⟨32,99935715,99935770⟩,
⟨64,199489460,199489568⟩]
theorem checked61943 : checkPrefixCuts (2^48) 8122925057 10 Manual.Count131072.C061943.packed 64 cuts61943 = true := by
 decide +kernel
def pointBounds61943 : List (Nat × Nat × Nat) := [(8122990592,114310151069471,114310539701792)]
theorem point_links_checked61943 : (cuts61943.take 1).map (fun c => (8122925057-1+2*2^10*c.k,114310051133756+c.lower,114310439766022+c.upper)) = pointBounds61943 := by
 decide +kernel
def cuts61944 : List PrefixCut := [⟨64,195501357,195501473⟩]
theorem checked61944 : checkPrefixCuts (2^48) 8123056129 10 Manual.Count131072.C061944.packed 64 cuts61944 = true := by
 decide +kernel
def cuts61945 : List PrefixCut := [⟨28,86314825,86314874⟩,
⟨64,197403982,197404098⟩]
theorem checked61945 : checkPrefixCuts (2^48) 8123187201 10 Manual.Count131072.C061945.packed 64 cuts61945 = true := by
 decide +kernel
def pointBounds61945 : List (Nat × Nat × Nat) := [(8123244544,114310532439398,114310921071937)]
theorem point_links_checked61945 : (cuts61945.take 1).map (fun c => (8123187201-1+2*2^10*c.k,114310446124573+c.lower,114310834757063+c.upper)) = pointBounds61945 := by
 decide +kernel
def cuts61946 : List PrefixCut := [⟨64,199306557,199306667⟩]
theorem checked61946 : checkPrefixCuts (2^48) 8123318273 10 Manual.Count131072.C061946.packed 64 cuts61946 = true := by
 decide +kernel
def cuts61947 : List PrefixCut := [⟨24,73699637,73699683⟩,
⟨64,197986642,197986762⟩]
theorem checked61947 : checkPrefixCuts (2^48) 8123449345 10 Manual.Count131072.C061947.packed 64 cuts61947 = true := by
 decide +kernel
def pointBounds61947 : List (Nat × Nat × Nat) := [(8123498496,114310916534749,114311305167511)]
theorem point_links_checked61947 : (cuts61947.take 1).map (fun c => (8123449345-1+2*2^10*c.k,114310842835112+c.lower,114311231467828+c.upper)) = pointBounds61947 := by
 decide +kernel
def cuts61948 : List PrefixCut := [⟨64,201794823,201794936⟩]
theorem checked61948 : checkPrefixCuts (2^48) 8123580417 10 Manual.Count131072.C061948.packed 64 cuts61948 = true := by
 decide +kernel
def cuts61949 : List PrefixCut := [⟨20,61085257,61085292⟩,
⟨64,198673226,198673338⟩]
theorem checked61949 : checkPrefixCuts (2^48) 8123711489 10 Manual.Count131072.C061949.packed 64 cuts61949 = true := by
 decide +kernel
def pointBounds61949 : List (Nat × Nat × Nat) := [(8123752448,114311303701834,114311692334818)]
theorem point_links_checked61949 : (cuts61949.take 1).map (fun c => (8123711489-1+2*2^10*c.k,114311242616577+c.lower,114311631249526+c.upper)) = pointBounds61949 := by
 decide +kernel
def cuts61950 : List PrefixCut := [⟨64,196348633,196348749⟩]
theorem checked61950 : checkPrefixCuts (2^48) 8123842561 10 Manual.Count131072.C061950.packed 64 cuts61950 = true := by
 decide +kernel
def cuts61951 : List PrefixCut := [⟨16,49753626,49753656⟩,
⟨64,201438590,201438710⟩]
theorem checked61951 : checkPrefixCuts (2^48) 8123973633 10 Manual.Count131072.C061951.packed 64 cuts61951 = true := by
 decide +kernel
def pointBounds61951 : List (Nat × Nat × Nat) := [(8124006400,114311687392062,114312076025269)]
theorem point_links_checked61951 : (cuts61951.take 1).map (fun c => (8123973633-1+2*2^10*c.k,114311637638436+c.lower,114312026271613+c.upper)) = pointBounds61951 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S7.B000060
