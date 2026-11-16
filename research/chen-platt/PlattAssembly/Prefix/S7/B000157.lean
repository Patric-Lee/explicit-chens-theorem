import PlattAssemblyKernel
import PlattCertificates.Count131072.C065024
import PlattCertificates.Count131072.C065025
import PlattCertificates.Count131072.C065026
import PlattCertificates.Count131072.C065027
import PlattCertificates.Count131072.C065028
import PlattCertificates.Count131072.C065029
import PlattCertificates.Count131072.C065030
import PlattCertificates.Count131072.C065031
import PlattCertificates.Count131072.C065032
import PlattCertificates.Count131072.C065033
import PlattCertificates.Count131072.C065034
import PlattCertificates.Count131072.C065035
import PlattCertificates.Count131072.C065036
import PlattCertificates.Count131072.C065037
import PlattCertificates.Count131072.C065038
import PlattCertificates.Count131072.C065039
import PlattCertificates.Count131072.C065040
import PlattCertificates.Count131072.C065041
import PlattCertificates.Count131072.C065042
import PlattCertificates.Count131072.C065043
import PlattCertificates.Count131072.C065044
import PlattCertificates.Count131072.C065045
import PlattCertificates.Count131072.C065046
import PlattCertificates.Count131072.C065047
import PlattCertificates.Count131072.C065048
import PlattCertificates.Count131072.C065049
import PlattCertificates.Count131072.C065050
import PlattCertificates.Count131072.C065051
import PlattCertificates.Count131072.C065052
import PlattCertificates.Count131072.C065053
import PlattCertificates.Count131072.C065054
import PlattCertificates.Count131072.C065055
namespace ChenEffective.PlattWindow.Assembly.Prefix.S7.B000157
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts65024 : List PrefixCut := [⟨64,189084274,189084378⟩]
theorem checked65024 : checkPrefixCuts (2^48) 8526757889 10 Manual.Count131072.C065024.packed 64 cuts65024 = true := by
 decide +kernel
def cuts65025 : List PrefixCut := [⟨37,108735339,108735404⟩,
⟨64,188718253,188718364⟩]
theorem checked65025 : checkPrefixCuts (2^48) 8526888961 10 Manual.Count131072.C065025.packed 64 cuts65025 = true := by
 decide +kernel
def pointBounds65025 : List (Nat × Nat × Nat) := [(8526964736,114908251800453,114908640777303)]
theorem point_links_checked65025 : (cuts65025.take 1).map (fun c => (8526888961-1+2*2^10*c.k,114908143065114+c.lower,114908532041899+c.upper)) = pointBounds65025 := by
 decide +kernel
def cuts65026 : List PrefixCut := [⟨64,190728927,190729039⟩]
theorem checked65026 : checkPrefixCuts (2^48) 8527020033 10 Manual.Count131072.C065026.packed 64 cuts65026 = true := by
 decide +kernel
def cuts65027 : List PrefixCut := [⟨40,118139552,118139620⟩,
⟨64,188514404,188514510⟩]
theorem checked65027 : checkPrefixCuts (2^48) 8527151105 10 Manual.Count131072.C065027.packed 64 cuts65027 = true := by
 decide +kernel
def pointBounds65027 : List (Nat × Nat × Nat) := [(8527233024,114908640651846,114909029628922)]
theorem point_links_checked65027 : (cuts65027.take 1).map (fun c => (8527151105-1+2*2^10*c.k,114908522512294+c.lower,114908911489302+c.upper)) = pointBounds65027 := by
 decide +kernel
def cuts65028 : List PrefixCut := [⟨64,187686287,187686399⟩]
theorem checked65028 : checkPrefixCuts (2^48) 8527282177 10 Manual.Count131072.C065028.packed 64 cuts65028 = true := by
 decide +kernel
def cuts65029 : List PrefixCut := [⟨43,127246110,127246184⟩,
⟨64,189795920,189796029⟩]
theorem checked65029 : checkPrefixCuts (2^48) 8527413249 10 Manual.Count131072.C065029.packed 64 cuts65029 = true := by
 decide +kernel
def pointBounds65029 : List (Nat × Nat × Nat) := [(8527501312,114909025959095,114909414936395)]
theorem point_links_checked65029 : (cuts65029.take 1).map (fun c => (8527413249-1+2*2^10*c.k,114908898712985+c.lower,114909287690211+c.upper)) = pointBounds65029 := by
 decide +kernel
def cuts65030 : List PrefixCut := [⟨64,189066837,189066943⟩]
theorem checked65030 : checkPrefixCuts (2^48) 8527544321 10 Manual.Count131072.C065030.packed 64 cuts65030 = true := by
 decide +kernel
def cuts65031 : List PrefixCut := [⟨46,136286076,136286155⟩,
⟨64,188733864,188733973⟩]
theorem checked65031 : checkPrefixCuts (2^48) 8527675393 10 Manual.Count131072.C065031.packed 64 cuts65031 = true := by
 decide +kernel
def pointBounds65031 : List (Nat × Nat × Nat) := [(8527769600,114909413861818,114909802839338)]
theorem point_links_checked65031 : (cuts65031.take 1).map (fun c => (8527675393-1+2*2^10*c.k,114909277575742+c.lower,114909666553183+c.upper)) = pointBounds65031 := by
 decide +kernel
def cuts65032 : List PrefixCut := [⟨64,187938800,187938911⟩]
theorem checked65032 : checkPrefixCuts (2^48) 8527806465 10 Manual.Count131072.C065032.packed 64 cuts65032 = true := by
 decide +kernel
def cuts65033 : List PrefixCut := [⟨49,144137265,144137350⟩,
⟨64,189520188,189520298⟩]
theorem checked65033 : checkPrefixCuts (2^48) 8527937537 10 Manual.Count131072.C065033.packed 64 cuts65033 = true := by
 decide +kernel
def pointBounds65033 : List (Nat × Nat × Nat) := [(8528037888,114909798385671,114910187363417)]
theorem point_links_checked65033 : (cuts65033.take 1).map (fun c => (8527937537-1+2*2^10*c.k,114909654248406+c.lower,114910043226067+c.upper)) = pointBounds65033 := by
 decide +kernel
def cuts65034 : List PrefixCut := [⟨64,188989202,188989312⟩]
theorem checked65034 : checkPrefixCuts (2^48) 8528068609 10 Manual.Count131072.C065034.packed 64 cuts65034 = true := by
 decide +kernel
def cuts65035 : List PrefixCut := [⟨52,153869264,153869350⟩,
⟨64,188194187,188194294⟩]
theorem checked65035 : checkPrefixCuts (2^48) 8528199681 10 Manual.Count131072.C065035.packed 64 cuts65035 = true := by
 decide +kernel
def pointBounds65035 : List (Nat × Nat × Nat) := [(8528306176,114910186627060,114910575605027)]
theorem point_links_checked65035 : (cuts65035.take 1).map (fun c => (8528199681-1+2*2^10*c.k,114910032757796+c.lower,114910421735677+c.upper)) = pointBounds65035 := by
 decide +kernel
def cuts65036 : List PrefixCut := [⟨64,190171547,190171666⟩]
theorem checked65036 : checkPrefixCuts (2^48) 8528330753 10 Manual.Count131072.C065036.packed 64 cuts65036 = true := by
 decide +kernel
def cuts65037 : List PrefixCut := [⟨55,162907565,162907661⟩,
⟨64,190597677,190597790⟩]
theorem checked65037 : checkPrefixCuts (2^48) 8528461825 10 Manual.Count131072.C065037.packed 64 cuts65037 = true := by
 decide +kernel
def pointBounds65037 : List (Nat × Nat × Nat) := [(8528574464,114910574031095,114910963009298)]
theorem point_links_checked65037 : (cuts65037.take 1).map (fun c => (8528461825-1+2*2^10*c.k,114910411123530+c.lower,114910800101637+c.upper)) = pointBounds65037 := by
 decide +kernel
def cuts65038 : List PrefixCut := [⟨64,189835668,189835776⟩]
theorem checked65038 : checkPrefixCuts (2^48) 8528592897 10 Manual.Count131072.C065038.packed 64 cuts65038 = true := by
 decide +kernel
def cuts65039 : List PrefixCut := [⟨58,168347965,168348062⟩,
⟨64,186895473,186895581⟩]
theorem checked65039 : checkPrefixCuts (2^48) 8528723969 10 Manual.Count131072.C065039.packed 64 cuts65039 = true := by
 decide +kernel
def pointBounds65039 : List (Nat × Nat × Nat) := [(8528842752,114910959904840,114911348883265)]
theorem point_links_checked65039 : (cuts65039.take 1).map (fun c => (8528723969-1+2*2^10*c.k,114910791556875+c.lower,114911180535203+c.upper)) = pointBounds65039 := by
 decide +kernel
def cuts65040 : List PrefixCut := [⟨64,190126851,190126956⟩]
theorem checked65040 : checkPrefixCuts (2^48) 8528855041 10 Manual.Count131072.C065040.packed 64 cuts65040 = true := by
 decide +kernel
def cuts65041 : List PrefixCut := [⟨61,178507339,178507437⟩,
⟨64,187021766,187021869⟩]
theorem checked65041 : checkPrefixCuts (2^48) 8528986113 10 Manual.Count131072.C065041.packed 64 cuts65041 = true := by
 decide +kernel
def pointBounds65041 : List (Nat × Nat × Nat) := [(8529111040,114911347086538,114911736065177)]
theorem point_links_checked65041 : (cuts65041.take 1).map (fun c => (8528986113-1+2*2^10*c.k,114911168579199+c.lower,114911557557740+c.upper)) = pointBounds65041 := by
 decide +kernel
def cuts65042 : List PrefixCut := [⟨64,188998977,188999090⟩]
theorem checked65042 : checkPrefixCuts (2^48) 8529117185 10 Manual.Count131072.C065042.packed 64 cuts65042 = true := by
 decide +kernel
def cuts65043 : List PrefixCut := [⟨64,189821084,189821193⟩]
theorem checked65043 : checkPrefixCuts (2^48) 8529248257 10 Manual.Count131072.C065043.packed 64 cuts65043 = true := by
 decide +kernel
def pointBounds65043 : List (Nat × Nat × Nat) := [(8529379328,114911734421026,114912123399892)]
theorem point_links_checked65043 : (cuts65043.take 1).map (fun c => (8529248257-1+2*2^10*c.k,114911544599942+c.lower,114911933578699+c.upper)) = pointBounds65043 := by
 decide +kernel
def cuts65044 : List PrefixCut := [⟨64,189818154,189818264⟩]
theorem checked65044 : checkPrefixCuts (2^48) 8529379329 10 Manual.Count131072.C065044.packed 64 cuts65044 = true := by
 decide +kernel
def cuts65045 : List PrefixCut := [⟨64,188561251,188561363⟩]
theorem checked65045 : checkPrefixCuts (2^48) 8529510401 10 Manual.Count131072.C065045.packed 64 cuts65045 = true := by
 decide +kernel
def cuts65046 : List PrefixCut := [⟨3,9272889,9272894⟩,
⟨64,190043334,190043442⟩]
theorem checked65046 : checkPrefixCuts (2^48) 8529641473 10 Manual.Count131072.C065046.packed 64 cuts65046 = true := by
 decide +kernel
def pointBounds65046 : List (Nat × Nat × Nat) := [(8529647616,114912122073320,114912511052413)]
theorem point_links_checked65046 : (cuts65046.take 1).map (fun c => (8529641473-1+2*2^10*c.k,114912112800431+c.lower,114912501779519+c.upper)) = pointBounds65046 := by
 decide +kernel
def cuts65047 : List PrefixCut := [⟨64,189281445,189281549⟩]
theorem checked65047 : checkPrefixCuts (2^48) 8529772545 10 Manual.Count131072.C065047.packed 64 cuts65047 = true := by
 decide +kernel
def cuts65048 : List PrefixCut := [⟨6,18644197,18644208⟩,
⟨64,188552558,188552672⟩]
theorem checked65048 : checkPrefixCuts (2^48) 8529903617 10 Manual.Count131072.C065048.packed 64 cuts65048 = true := by
 decide +kernel
def pointBounds65048 : List (Nat × Nat × Nat) := [(8529915904,114912510769407,114912899748718)]
theorem point_links_checked65048 : (cuts65048.take 1).map (fun c => (8529903617-1+2*2^10*c.k,114912492125210+c.lower,114912881104510+c.upper)) = pointBounds65048 := by
 decide +kernel
def cuts65049 : List PrefixCut := [⟨64,185678870,185678972⟩]
theorem checked65049 : checkPrefixCuts (2^48) 8530034689 10 Manual.Count131072.C065049.packed 64 cuts65049 = true := by
 decide +kernel
def cuts65050 : List PrefixCut := [⟨9,26035068,26035084⟩,
⟨64,188711751,188711858⟩]
theorem checked65050 : checkPrefixCuts (2^48) 8530165761 10 Manual.Count131072.C065050.packed 64 cuts65050 = true := by
 decide +kernel
def pointBounds65050 : List (Nat × Nat × Nat) := [(8530184192,114912892391706,114913281371238)]
theorem point_links_checked65050 : (cuts65050.take 1).map (fun c => (8530165761-1+2*2^10*c.k,114912866356638+c.lower,114913255336154+c.upper)) = pointBounds65050 := by
 decide +kernel
def cuts65051 : List PrefixCut := [⟨64,185706130,185706242⟩]
theorem checked65051 : checkPrefixCuts (2^48) 8530296833 10 Manual.Count131072.C065051.packed 64 cuts65051 = true := by
 decide +kernel
def cuts65052 : List PrefixCut := [⟨12,35207294,35207314⟩,
⟨64,190751740,190751846⟩]
theorem checked65052 : checkPrefixCuts (2^48) 8530427905 10 Manual.Count131072.C065052.packed 64 cuts65052 = true := by
 decide +kernel
def pointBounds65052 : List (Nat × Nat × Nat) := [(8530452480,114913275981813,114913664961568)]
theorem point_links_checked65052 : (cuts65052.take 1).map (fun c => (8530427905-1+2*2^10*c.k,114913240774519+c.lower,114913629754254+c.upper)) = pointBounds65052 := by
 decide +kernel
def cuts65053 : List PrefixCut := [⟨64,188736049,188736158⟩]
theorem checked65053 : checkPrefixCuts (2^48) 8530558977 10 Manual.Count131072.C065053.packed 64 cuts65053 = true := by
 decide +kernel
def cuts65054 : List PrefixCut := [⟨15,43686046,43686070⟩,
⟨64,184773735,184773844⟩]
theorem checked65054 : checkPrefixCuts (2^48) 8530690049 10 Manual.Count131072.C065054.packed 64 cuts65054 = true := by
 decide +kernel
def pointBounds65054 : List (Nat × Nat × Nat) := [(8530720768,114913663948354,114914052928328)]
theorem point_links_checked65054 : (cuts65054.take 1).map (fun c => (8530690049-1+2*2^10*c.k,114913620262308+c.lower,114914009242258+c.upper)) = pointBounds65054 := by
 decide +kernel
def cuts65055 : List PrefixCut := [⟨64,186651583,186651695⟩]
theorem checked65055 : checkPrefixCuts (2^48) 8530821121 10 Manual.Count131072.C065055.packed 64 cuts65055 = true := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S7.B000157
