import PlattAssemblyKernel
import PlattCertificates.Count131072.C063936
import PlattCertificates.Count131072.C063937
import PlattCertificates.Count131072.C063938
import PlattCertificates.Count131072.C063939
import PlattCertificates.Count131072.C063940
import PlattCertificates.Count131072.C063941
import PlattCertificates.Count131072.C063942
import PlattCertificates.Count131072.C063943
import PlattCertificates.Count131072.C063944
import PlattCertificates.Count131072.C063945
import PlattCertificates.Count131072.C063946
import PlattCertificates.Count131072.C063947
import PlattCertificates.Count131072.C063948
import PlattCertificates.Count131072.C063949
import PlattCertificates.Count131072.C063950
import PlattCertificates.Count131072.C063951
import PlattCertificates.Count131072.C063952
import PlattCertificates.Count131072.C063953
import PlattCertificates.Count131072.C063954
import PlattCertificates.Count131072.C063955
import PlattCertificates.Count131072.C063956
import PlattCertificates.Count131072.C063957
import PlattCertificates.Count131072.C063958
import PlattCertificates.Count131072.C063959
import PlattCertificates.Count131072.C063960
import PlattCertificates.Count131072.C063961
import PlattCertificates.Count131072.C063962
import PlattCertificates.Count131072.C063963
import PlattCertificates.Count131072.C063964
import PlattCertificates.Count131072.C063965
import PlattCertificates.Count131072.C063966
import PlattCertificates.Count131072.C063967
namespace ChenEffective.PlattWindow.Assembly.Prefix.S7.B000123
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts63936 : List PrefixCut := [⟨48,145434173,145434256⟩,
⟨64,193777565,193777675⟩]
theorem checked63936 : checkPrefixCuts (2^48) 8384151553 10 Manual.Count131072.C063936.packed 64 cuts63936 = true := by
 decide +kernel
def pointBounds63936 : List (Nat × Nat × Nat) := [(8384249856,114700427666110,114700816522940)]
theorem point_links_checked63936 : (cuts63936.take 1).map (fun c => (8384151553-1+2*2^10*c.k,114700282231937+c.lower,114700671088684+c.upper)) = pointBounds63936 := by
 decide +kernel
def cuts63937 : List PrefixCut := [⟨64,191390952,191391060⟩]
theorem checked63937 : checkPrefixCuts (2^48) 8384282625 10 Manual.Count131072.C063937.packed 64 cuts63937 = true := by
 decide +kernel
def cuts63938 : List PrefixCut := [⟨48,140696109,140696195⟩,
⟨64,188299429,188299545⟩]
theorem checked63938 : checkPrefixCuts (2^48) 8384413697 10 Manual.Count131072.C063938.packed 64 cuts63938 = true := by
 decide +kernel
def pointBounds63938 : List (Nat × Nat × Nat) := [(8384512000,114700808096563,114701196953614)]
theorem point_links_checked63938 : (cuts63938.take 1).map (fun c => (8384413697-1+2*2^10*c.k,114700667400454+c.lower,114701056257419+c.upper)) = pointBounds63938 := by
 decide +kernel
def cuts63939 : List PrefixCut := [⟨64,193802042,193802151⟩]
theorem checked63939 : checkPrefixCuts (2^48) 8384544769 10 Manual.Count131072.C063939.packed 64 cuts63939 = true := by
 decide +kernel
def cuts63940 : List PrefixCut := [⟨48,143780154,143780230⟩,
⟨64,192859054,192859158⟩]
theorem checked63940 : checkPrefixCuts (2^48) 8384675841 10 Manual.Count131072.C063940.packed 64 cuts63940 = true := by
 decide +kernel
def pointBounds63940 : List (Nat × Nat × Nat) := [(8384774144,114701193282079,114701582139345)]
theorem point_links_checked63940 : (cuts63940.take 1).map (fun c => (8384675841-1+2*2^10*c.k,114701049501925+c.lower,114701438359115+c.upper)) = pointBounds63940 := by
 decide +kernel
def cuts63941 : List PrefixCut := [⟨64,193393141,193393251⟩]
theorem checked63941 : checkPrefixCuts (2^48) 8384806913 10 Manual.Count131072.C063941.packed 64 cuts63941 = true := by
 decide +kernel
def cuts63942 : List PrefixCut := [⟨48,143070697,143070782⟩,
⟨64,192181631,192181745⟩]
theorem checked63942 : checkPrefixCuts (2^48) 8384937985 10 Manual.Count131072.C063942.packed 64 cuts63942 = true := by
 decide +kernel
def pointBounds63942 : List (Nat × Nat × Nat) := [(8385036288,114701578824817,114701967682306)]
theorem point_links_checked63942 : (cuts63942.take 1).map (fun c => (8384937985-1+2*2^10*c.k,114701435754120+c.lower,114701824611524+c.upper)) = pointBounds63942 := by
 decide +kernel
def cuts63943 : List PrefixCut := [⟨64,190298816,190298926⟩]
theorem checked63943 : checkPrefixCuts (2^48) 8385069057 10 Manual.Count131072.C063943.packed 64 cuts63943 = true := by
 decide +kernel
def cuts63944 : List PrefixCut := [⟨48,142361294,142361375⟩,
⟨64,189758747,189758856⟩]
theorem checked63944 : checkPrefixCuts (2^48) 8385200129 10 Manual.Count131072.C063944.packed 64 cuts63944 = true := by
 decide +kernel
def pointBounds63944 : List (Nat × Nat × Nat) := [(8385298432,114701960595861,114702349453570)]
theorem point_links_checked63944 : (cuts63944.take 1).map (fun c => (8385200129-1+2*2^10*c.k,114701818234567+c.lower,114702207092195+c.upper)) = pointBounds63944 := by
 decide +kernel
def cuts63945 : List PrefixCut := [⟨64,193951709,193951816⟩]
theorem checked63945 : checkPrefixCuts (2^48) 8385331201 10 Manual.Count131072.C063945.packed 64 cuts63945 = true := by
 decide +kernel
def cuts63946 : List PrefixCut := [⟨48,144001636,144001711⟩,
⟨64,190054944,190055046⟩]
theorem checked63946 : checkPrefixCuts (2^48) 8385462273 10 Manual.Count131072.C063946.packed 64 cuts63946 = true := by
 decide +kernel
def pointBounds63946 : List (Nat × Nat × Nat) := [(8385560576,114702345946659,114702734804578)]
theorem point_links_checked63946 : (cuts63946.take 1).map (fun c => (8385462273-1+2*2^10*c.k,114702201945023+c.lower,114702590802867+c.upper)) = pointBounds63946 := by
 decide +kernel
def cuts63947 : List PrefixCut := [⟨64,194986197,194986306⟩]
theorem checked63947 : checkPrefixCuts (2^48) 8385593345 10 Manual.Count131072.C063947.packed 64 cuts63947 = true := by
 decide +kernel
def cuts63948 : List PrefixCut := [⟨48,143426512,143426602⟩,
⟨64,191962229,191962347⟩]
theorem checked63948 : checkPrefixCuts (2^48) 8385724417 10 Manual.Count131072.C063948.packed 64 cuts63948 = true := by
 decide +kernel
def pointBounds63948 : List (Nat × Nat × Nat) := [(8385822720,114702730412676,114703119270821)]
theorem point_links_checked63948 : (cuts63948.take 1).map (fun c => (8385724417-1+2*2^10*c.k,114702586986164+c.lower,114702975844219+c.upper)) = pointBounds63948 := by
 decide +kernel
def cuts63949 : List PrefixCut := [⟨64,192496266,192496379⟩]
theorem checked63949 : checkPrefixCuts (2^48) 8385855489 10 Manual.Count131072.C063949.packed 64 cuts63949 = true := by
 decide +kernel
def cuts63950 : List PrefixCut := [⟨48,145066708,145066788⟩,
⟨64,193533777,193533887⟩]
theorem checked63950 : checkPrefixCuts (2^48) 8385986561 10 Manual.Count131072.C063950.packed 64 cuts63950 = true := by
 decide +kernel
def pointBounds63950 : List (Nat × Nat × Nat) := [(8386084864,114703116511367,114703505369733)]
theorem point_links_checked63950 : (cuts63950.take 1).map (fun c => (8385986561-1+2*2^10*c.k,114702971444659+c.lower,114703360302945+c.upper)) = pointBounds63950 := by
 decide +kernel
def cuts63951 : List PrefixCut := [⟨64,192356021,192356129⟩]
theorem checked63951 : checkPrefixCuts (2^48) 8386117633 10 Manual.Count131072.C063951.packed 64 cuts63951 = true := by
 decide +kernel
def cuts63952 : List PrefixCut := [⟨48,142477754,142477840⟩,
⟨64,190943306,190943420⟩]
theorem checked63952 : checkPrefixCuts (2^48) 8386248705 10 Manual.Count131072.C063952.packed 64 cuts63952 = true := by
 decide +kernel
def pointBounds63952 : List (Nat × Nat × Nat) := [(8386347008,114703499812211,114703888670801)]
theorem point_links_checked63952 : (cuts63952.take 1).map (fun c => (8386248705-1+2*2^10*c.k,114703357334457+c.lower,114703746192961+c.upper)) = pointBounds63952 := by
 decide +kernel
def cuts63953 : List PrefixCut := [⟨64,194363762,194363879⟩]
theorem checked63953 : checkPrefixCuts (2^48) 8386379777 10 Manual.Count131072.C063953.packed 64 cuts63953 = true := by
 decide +kernel
def cuts63954 : List PrefixCut := [⟨48,142506865,142506951⟩,
⟨64,190165405,190165520⟩]
theorem checked63954 : checkPrefixCuts (2^48) 8386510849 10 Manual.Count131072.C063954.packed 64 cuts63954 = true := by
 decide +kernel
def pointBounds63954 : List (Nat × Nat × Nat) := [(8386609152,114703885148390,114704274007211)]
theorem point_links_checked63954 : (cuts63954.take 1).map (fun c => (8386510849-1+2*2^10*c.k,114703742641525+c.lower,114704131500260+c.upper)) = pointBounds63954 := by
 decide +kernel
def cuts63955 : List PrefixCut := [⟨64,191269986,191270099⟩]
theorem checked63955 : checkPrefixCuts (2^48) 8386641921 10 Manual.Count131072.C063955.packed 64 cuts63955 = true := by
 decide +kernel
def cuts63956 : List PrefixCut := [⟨48,145388712,145388793⟩,
⟨64,192978642,192978751⟩]
theorem checked63956 : checkPrefixCuts (2^48) 8386772993 10 Manual.Count131072.C063956.packed 64 cuts63956 = true := by
 decide +kernel
def pointBounds63956 : List (Nat × Nat × Nat) := [(8386871296,114704269465628,114704658324672)]
theorem point_links_checked63956 : (cuts63956.take 1).map (fun c => (8386772993-1+2*2^10*c.k,114704124076916+c.lower,114704512935879+c.upper)) = pointBounds63956 := by
 decide +kernel
def cuts63957 : List PrefixCut := [⟨64,192170163,192170274⟩]
theorem checked63957 : checkPrefixCuts (2^48) 8386904065 10 Manual.Count131072.C063957.packed 64 cuts63957 = true := by
 decide +kernel
def cuts63958 : List PrefixCut := [⟨48,143907499,143907586⟩,
⟨64,191797984,191798097⟩]
theorem checked63958 : checkPrefixCuts (2^48) 8387035137 10 Manual.Count131072.C063958.packed 64 cuts63958 = true := by
 decide +kernel
def pointBounds63958 : List (Nat × Nat × Nat) := [(8387133440,114704653133220,114705041992490)]
theorem point_links_checked63958 : (cuts63958.take 1).map (fun c => (8387035137-1+2*2^10*c.k,114704509225721+c.lower,114704898084904+c.upper)) = pointBounds63958 := by
 decide +kernel
def cuts63959 : List PrefixCut := [⟨64,191794989,191795101⟩]
theorem checked63959 : checkPrefixCuts (2^48) 8387166209 10 Manual.Count131072.C063959.packed 64 cuts63959 = true := by
 decide +kernel
def cuts63960 : List PrefixCut := [⟨48,144305703,144305792⟩,
⟨64,192664520,192664639⟩]
theorem checked63960 : checkPrefixCuts (2^48) 8387297281 10 Manual.Count131072.C063960.packed 64 cuts63960 = true := by
 decide +kernel
def pointBounds63960 : List (Nat × Nat × Nat) := [(8387395584,114705037124397,114705425983894)]
theorem point_links_checked63960 : (cuts63960.take 1).map (fun c => (8387297281-1+2*2^10*c.k,114704892818694+c.lower,114705281678102+c.upper)) = pointBounds63960 := by
 decide +kernel
def cuts63961 : List PrefixCut := [⟨64,194708621,194708736⟩]
theorem checked63961 : checkPrefixCuts (2^48) 8387428353 10 Manual.Count131072.C063961.packed 64 cuts63961 = true := by
 decide +kernel
def cuts63962 : List PrefixCut := [⟨48,143663604,143663689⟩,
⟨64,192121588,192121703⟩]
theorem checked63962 : checkPrefixCuts (2^48) 8387559425 10 Manual.Count131072.C063962.packed 64 cuts63962 = true := by
 decide +kernel
def pointBounds63962 : List (Nat × Nat × Nat) := [(8387657728,114705423855439,114705812715166)]
theorem point_links_checked63962 : (cuts63962.take 1).map (fun c => (8387559425-1+2*2^10*c.k,114705280191835+c.lower,114705669051477+c.upper)) = pointBounds63962 := by
 decide +kernel
def cuts63963 : List PrefixCut := [⟨64,192823287,192823395⟩]
theorem checked63963 : checkPrefixCuts (2^48) 8387690497 10 Manual.Count131072.C063963.packed 64 cuts63963 = true := by
 decide +kernel
def cuts63964 : List PrefixCut := [⟨48,141914117,141914205⟩,
⟨64,190907495,190907613⟩]
theorem checked63964 : checkPrefixCuts (2^48) 8387821569 10 Manual.Count131072.C063964.packed 64 cuts63964 = true := by
 decide +kernel
def pointBounds63964 : List (Nat × Nat × Nat) := [(8387919872,114705807050827,114706195910780)]
theorem point_links_checked63964 : (cuts63964.take 1).map (fun c => (8387821569-1+2*2^10*c.k,114705665136710+c.lower,114706053996575+c.upper)) = pointBounds63964 := by
 decide +kernel
def cuts63965 : List PrefixCut := [⟨64,192213248,192213352⟩]
theorem checked63965 : checkPrefixCuts (2^48) 8387952641 10 Manual.Count131072.C063965.packed 64 cuts63965 = true := by
 decide +kernel
def cuts63966 : List PrefixCut := [⟨48,144627747,144627832⟩,
⟨64,193015588,193015700⟩]
theorem checked63966 : checkPrefixCuts (2^48) 8388083713 10 Manual.Count131072.C063966.packed 64 cuts63966 = true := by
 decide +kernel
def pointBounds63966 : List (Nat × Nat × Nat) := [(8388182016,114706192885200,114706581745372)]
theorem point_links_checked63966 : (cuts63966.take 1).map (fun c => (8388083713-1+2*2^10*c.k,114706048257453+c.lower,114706437117540+c.upper)) = pointBounds63966 := by
 decide +kernel
def cuts63967 : List PrefixCut := [⟨64,195160152,195160262⟩]
theorem checked63967 : checkPrefixCuts (2^48) 8388214785 10 Manual.Count131072.C063967.packed 64 cuts63967 = true := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S7.B000123
