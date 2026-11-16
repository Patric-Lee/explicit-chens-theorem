import PlattAssemblyKernel
import PlattCertificates.Count131072.C073936
import PlattCertificates.Count131072.C073937
import PlattCertificates.Count131072.C073938
import PlattCertificates.Count131072.C073939
import PlattCertificates.Count131072.C073940
import PlattCertificates.Count131072.C073941
import PlattCertificates.Count131072.C073942
import PlattCertificates.Count131072.C073943
import PlattCertificates.Count131072.C073944
import PlattCertificates.Count131072.C073945
import PlattCertificates.Count131072.C073946
import PlattCertificates.Count131072.C073947
import PlattCertificates.Count131072.C073948
import PlattCertificates.Count131072.C073949
import PlattCertificates.Count131072.C073950
import PlattCertificates.Count131072.C073951
import PlattCertificates.Count131072.C073952
import PlattCertificates.Count131072.C073953
import PlattCertificates.Count131072.C073954
import PlattCertificates.Count131072.C073955
import PlattCertificates.Count131072.C073956
import PlattCertificates.Count131072.C073957
import PlattCertificates.Count131072.C073958
import PlattCertificates.Count131072.C073959
import PlattCertificates.Count131072.C073960
import PlattCertificates.Count131072.C073961
import PlattCertificates.Count131072.C073962
import PlattCertificates.Count131072.C073963
import PlattCertificates.Count131072.C073964
import PlattCertificates.Count131072.C073965
import PlattCertificates.Count131072.C073966
import PlattCertificates.Count131072.C073967
namespace ChenEffective.PlattWindow.Assembly.Prefix.S8.B000123
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts73936 : List PrefixCut := [⟨2,5400208,5400211⟩,
⟨64,165402051,165402153⟩]
theorem checked73936 : checkPrefixCuts (2^48) 9694871553 10 Manual.Count131072.C073936.packed 64 cuts73936 = true := by
 decide +kernel
def pointBounds73936 : List (Nat × Nat × Nat) := [(9694875648,116483940388380,116484330291170)]
theorem point_links_checked73936 : (cuts73936.take 1).map (fun c => (9694871553-1+2*2^10*c.k,116483934988172+c.lower,116484324890959+c.upper)) = pointBounds73936 := by
 decide +kernel
def cuts73937 : List PrefixCut := [⟨64,164180430,164180534⟩]
theorem checked73937 : checkPrefixCuts (2^48) 9695002625 10 Manual.Count131072.C073937.packed 64 cuts73937 = true := by
 decide +kernel
def cuts73938 : List PrefixCut := [⟨22,58645703,58645740⟩,
⟨64,167226622,167226727⟩]
theorem checked73938 : checkPrefixCuts (2^48) 9695133697 10 Manual.Count131072.C073938.packed 64 cuts73938 = true := by
 decide +kernel
def pointBounds73938 : List (Nat × Nat × Nat) := [(9695178752,116484323216356,116484713119386)]
theorem point_links_checked73938 : (cuts73938.take 1).map (fun c => (9695133697-1+2*2^10*c.k,116484264570653+c.lower,116484654473646+c.upper)) = pointBounds73938 := by
 decide +kernel
def cuts73939 : List PrefixCut := [⟨64,165105015,165105116⟩]
theorem checked73939 : checkPrefixCuts (2^48) 9695264769 10 Manual.Count131072.C073939.packed 64 cuts73939 = true := by
 decide +kernel
def cuts73940 : List PrefixCut := [⟨42,107591413,107591479⟩,
⟨64,164347971,164348069⟩]
theorem checked73940 : checkPrefixCuts (2^48) 9695395841 10 Manual.Count131072.C073940.packed 64 cuts73940 = true := by
 decide +kernel
def pointBounds73940 : List (Nat × Nat × Nat) := [(9695481856,116484704493703,116485094396968)]
theorem point_links_checked73940 : (cuts73940.take 1).map (fun c => (9695395841-1+2*2^10*c.k,116484596902290+c.lower,116484986805489+c.upper)) = pointBounds73940 := by
 decide +kernel
def cuts73941 : List PrefixCut := [⟨64,164955398,164955496⟩]
theorem checked73941 : checkPrefixCuts (2^48) 9695526913 10 Manual.Count131072.C073941.packed 64 cuts73941 = true := by
 decide +kernel
def cuts73942 : List PrefixCut := [⟨62,159379287,159379381⟩,
⟨64,164633833,164633930⟩]
theorem checked73942 : checkPrefixCuts (2^48) 9695657985 10 Manual.Count131072.C073942.packed 64 cuts73942 = true := by
 decide +kernel
def pointBounds73942 : List (Nat × Nat × Nat) := [(9695784960,116485085584946,116485475488435)]
theorem point_links_checked73942 : (cuts73942.take 1).map (fun c => (9695657985-1+2*2^10*c.k,116484926205659+c.lower,116485316109054+c.upper)) = pointBounds73942 := by
 decide +kernel
def cuts73943 : List PrefixCut := [⟨64,164863860,164863958⟩]
theorem checked73943 : checkPrefixCuts (2^48) 9695789057 10 Manual.Count131072.C073943.packed 64 cuts73943 = true := by
 decide +kernel
def cuts73944 : List PrefixCut := [⟨64,165151933,165152033⟩]
theorem checked73944 : checkPrefixCuts (2^48) 9695920129 10 Manual.Count131072.C073944.packed 64 cuts73944 = true := by
 decide +kernel
def cuts73945 : List PrefixCut := [⟨18,46766996,46767025⟩,
⟨64,164307830,164307928⟩]
theorem checked73945 : checkPrefixCuts (2^48) 9696051201 10 Manual.Count131072.C073945.packed 64 cuts73945 = true := by
 decide +kernel
def pointBounds73945 : List (Nat × Nat × Nat) := [(9696088064,116485467622281,116485857526000)]
theorem point_links_checked73945 : (cuts73945.take 1).map (fun c => (9696051201-1+2*2^10*c.k,116485420855285+c.lower,116485810758975+c.upper)) = pointBounds73945 := by
 decide +kernel
def cuts73946 : List PrefixCut := [⟨64,166424740,166424840⟩]
theorem checked73946 : checkPrefixCuts (2^48) 9696182273 10 Manual.Count131072.C073946.packed 64 cuts73946 = true := by
 decide +kernel
def cuts73947 : List PrefixCut := [⟨38,97885604,97885665⟩,
⟨64,164854934,164855035⟩]
theorem checked73947 : checkPrefixCuts (2^48) 9696313345 10 Manual.Count131072.C073947.packed 64 cuts73947 = true := by
 decide +kernel
def pointBounds73947 : List (Nat × Nat × Nat) := [(9696391168,116485849473459,116486239377408)]
theorem point_links_checked73947 : (cuts73947.take 1).map (fun c => (9696313345-1+2*2^10*c.k,116485751587855+c.lower,116486141491743+c.upper)) = pointBounds73947 := by
 decide +kernel
def cuts73948 : List PrefixCut := [⟨64,167320122,167320219⟩]
theorem checked73948 : checkPrefixCuts (2^48) 9696444417 10 Manual.Count131072.C073948.packed 64 cuts73948 = true := by
 decide +kernel
def cuts73949 : List PrefixCut := [⟨58,149204440,149204527⟩,
⟨64,165169788,165169884⟩]
theorem checked73949 : checkPrefixCuts (2^48) 9696575489 10 Manual.Count131072.C073949.packed 64 cuts73949 = true := by
 decide +kernel
def pointBounds73949 : List (Nat × Nat × Nat) := [(9696694272,116486232967351,116486622871524)]
theorem point_links_checked73949 : (cuts73949.take 1).map (fun c => (9696575489-1+2*2^10*c.k,116486083762911+c.lower,116486473666997+c.upper)) = pointBounds73949 := by
 decide +kernel
def cuts73950 : List PrefixCut := [⟨64,164557984,164558085⟩]
theorem checked73950 : checkPrefixCuts (2^48) 9696706561 10 Manual.Count131072.C073950.packed 64 cuts73950 = true := by
 decide +kernel
def cuts73951 : List PrefixCut := [⟨64,164729910,164730008⟩]
theorem checked73951 : checkPrefixCuts (2^48) 9696837633 10 Manual.Count131072.C073951.packed 64 cuts73951 = true := by
 decide +kernel
def cuts73952 : List PrefixCut := [⟨14,35935497,35935520⟩,
⟨64,165134061,165134163⟩]
theorem checked73952 : checkPrefixCuts (2^48) 9696968705 10 Manual.Count131072.C073952.packed 64 cuts73952 = true := by
 decide +kernel
def pointBounds73952 : List (Nat × Nat × Nat) := [(9696997376,116486614156090,116487004060494)]
theorem point_links_checked73952 : (cuts73952.take 1).map (fun c => (9696968705-1+2*2^10*c.k,116486578220593+c.lower,116486968124974+c.upper)) = pointBounds73952 := by
 decide +kernel
def cuts73953 : List PrefixCut := [⟨64,166902444,166902547⟩]
theorem checked73953 : checkPrefixCuts (2^48) 9697099777 10 Manual.Count131072.C073953.packed 64 cuts73953 = true := by
 decide +kernel
def cuts73954 : List PrefixCut := [⟨34,87194740,87194789⟩,
⟨64,164171735,164171831⟩]
theorem checked73954 : checkPrefixCuts (2^48) 9697230849 10 Manual.Count131072.C073954.packed 64 cuts73954 = true := by
 decide +kernel
def pointBounds73954 : List (Nat × Nat × Nat) := [(9697300480,116486997451838,116487387356473)]
theorem point_links_checked73954 : (cuts73954.take 1).map (fun c => (9697230849-1+2*2^10*c.k,116486910257098+c.lower,116487300161684+c.upper)) = pointBounds73954 := by
 decide +kernel
def cuts73955 : List PrefixCut := [⟨64,163501939,163502035⟩]
theorem checked73955 : checkPrefixCuts (2^48) 9697361921 10 Manual.Count131072.C073955.packed 64 cuts73955 = true := by
 decide +kernel
def cuts73956 : List PrefixCut := [⟨54,142688696,142688780⟩,
⟨64,168404997,168405097⟩]
theorem checked73956 : checkPrefixCuts (2^48) 9697492993 10 Manual.Count131072.C073956.packed 64 cuts73956 = true := by
 decide +kernel
def pointBounds73956 : List (Nat × Nat × Nat) := [(9697603584,116487380619468,116487770524330)]
theorem point_links_checked73956 : (cuts73956.take 1).map (fun c => (9697492993-1+2*2^10*c.k,116487237930772+c.lower,116487627835550+c.upper)) = pointBounds73956 := by
 decide +kernel
def cuts73957 : List PrefixCut := [⟨64,165790471,165790571⟩]
theorem checked73957 : checkPrefixCuts (2^48) 9697624065 10 Manual.Count131072.C073957.packed 64 cuts73957 = true := by
 decide +kernel
def cuts73958 : List PrefixCut := [⟨64,166310681,166310784⟩]
theorem checked73958 : checkPrefixCuts (2^48) 9697755137 10 Manual.Count131072.C073958.packed 64 cuts73958 = true := by
 decide +kernel
def cuts73959 : List PrefixCut := [⟨10,26121893,26121906⟩,
⟨64,169036702,169036797⟩]
theorem checked73959 : checkPrefixCuts (2^48) 9697886209 10 Manual.Count131072.C073959.packed 64 cuts73959 = true := by
 decide +kernel
def pointBounds73959 : List (Nat × Nat × Nat) := [(9697906688,116487764558814,116488154463908)]
theorem point_links_checked73959 : (cuts73959.take 1).map (fun c => (9697886209-1+2*2^10*c.k,116487738436921+c.lower,116488128342002+c.upper)) = pointBounds73959 := by
 decide +kernel
def cuts73960 : List PrefixCut := [⟨64,165464501,165464602⟩]
theorem checked73960 : checkPrefixCuts (2^48) 9698017281 10 Manual.Count131072.C073960.packed 64 cuts73960 = true := by
 decide +kernel
def cuts73961 : List PrefixCut := [⟨30,78131203,78131248⟩,
⟨64,166623191,166623289⟩]
theorem checked73961 : checkPrefixCuts (2^48) 9698148353 10 Manual.Count131072.C073961.packed 64 cuts73961 = true := by
 decide +kernel
def pointBounds73961 : List (Nat × Nat × Nat) := [(9698209792,116488151069327,116488540974649)]
theorem point_links_checked73961 : (cuts73961.take 1).map (fun c => (9698148353-1+2*2^10*c.k,116488072938124+c.lower,116488462843401+c.upper)) = pointBounds73961 := by
 decide +kernel
def cuts73962 : List PrefixCut := [⟨64,167926975,167927082⟩]
theorem checked73962 : checkPrefixCuts (2^48) 9698279425 10 Manual.Count131072.C073962.packed 64 cuts73962 = true := by
 decide +kernel
def cuts73963 : List PrefixCut := [⟨50,129557030,129557109⟩,
⟨64,164296886,164296988⟩]
theorem checked73963 : checkPrefixCuts (2^48) 9698410497 10 Manual.Count131072.C073963.packed 64 cuts73963 = true := by
 decide +kernel
def pointBounds73963 : List (Nat × Nat × Nat) := [(9698512896,116488537045320,116488926950881)]
theorem point_links_checked73963 : (cuts73963.take 1).map (fun c => (9698410497-1+2*2^10*c.k,116488407488290+c.lower,116488797393772+c.upper)) = pointBounds73963 := by
 decide +kernel
def cuts73964 : List PrefixCut := [⟨64,167138836,167138939⟩]
theorem checked73964 : checkPrefixCuts (2^48) 9698541569 10 Manual.Count131072.C073964.packed 64 cuts73964 = true := by
 decide +kernel
def cuts73965 : List PrefixCut := [⟨64,166323968,166324060⟩]
theorem checked73965 : checkPrefixCuts (2^48) 9698672641 10 Manual.Count131072.C073965.packed 64 cuts73965 = true := by
 decide +kernel
def cuts73966 : List PrefixCut := [⟨6,15932854,15932863⟩,
⟨64,165218909,165219003⟩]
theorem checked73966 : checkPrefixCuts (2^48) 9698803713 10 Manual.Count131072.C073966.packed 64 cuts73966 = true := by
 decide +kernel
def pointBounds73966 : List (Nat × Nat × Nat) := [(9698816000,116488921180834,116489311086622)]
theorem point_links_checked73966 : (cuts73966.take 1).map (fun c => (9698803713-1+2*2^10*c.k,116488905247980+c.lower,116489295153759+c.upper)) = pointBounds73966 := by
 decide +kernel
def cuts73967 : List PrefixCut := [⟨64,164462135,164462231⟩]
theorem checked73967 : checkPrefixCuts (2^48) 9698934785 10 Manual.Count131072.C073967.packed 64 cuts73967 = true := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S8.B000123
