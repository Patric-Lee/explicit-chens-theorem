import PlattAssemblyKernel
import PlattCertificates.Count131072.C046080
import PlattCertificates.Count131072.C046081
import PlattCertificates.Count131072.C046082
import PlattCertificates.Count131072.C046083
import PlattCertificates.Count131072.C046084
import PlattCertificates.Count131072.C046085
import PlattCertificates.Count131072.C046086
import PlattCertificates.Count131072.C046087
import PlattCertificates.Count131072.C046088
import PlattCertificates.Count131072.C046089
import PlattCertificates.Count131072.C046090
import PlattCertificates.Count131072.C046091
import PlattCertificates.Count131072.C046092
import PlattCertificates.Count131072.C046093
import PlattCertificates.Count131072.C046094
import PlattCertificates.Count131072.C046095
import PlattCertificates.Count131072.C046096
import PlattCertificates.Count131072.C046097
import PlattCertificates.Count131072.C046098
import PlattCertificates.Count131072.C046099
import PlattCertificates.Count131072.C046100
import PlattCertificates.Count131072.C046101
import PlattCertificates.Count131072.C046102
import PlattCertificates.Count131072.C046103
import PlattCertificates.Count131072.C046104
import PlattCertificates.Count131072.C046105
import PlattCertificates.Count131072.C046106
import PlattCertificates.Count131072.C046107
import PlattCertificates.Count131072.C046108
import PlattCertificates.Count131072.C046109
import PlattCertificates.Count131072.C046110
import PlattCertificates.Count131072.C046111
namespace ChenEffective.PlattWindow.Assembly.Prefix.S5.B000190
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts46080 : List PrefixCut := [⟨64,273939665,273939819⟩]
theorem checked46080 : checkPrefixCuts (2^48) 6043729921 10 Manual.Count131072.C046080.packed 64 cuts46080 = true := by
 decide +kernel
def cuts46081 : List PrefixCut := [⟨14,58354622,58354656⟩,
⟨64,269695702,269695856⟩]
theorem checked46081 : checkPrefixCuts (2^48) 6043860993 10 Manual.Count131072.C046081.packed 64 cuts46081 = true := by
 decide +kernel
def pointBounds46081 : List (Nat × Nat × Nat) := [(6043889664,110639299558669,110639686098804)]
theorem point_links_checked46081 : (cuts46081.take 1).map (fun c => (6043860993-1+2*2^10*c.k,110639241204047+c.lower,110639627744148+c.upper)) = pointBounds46081 := by
 decide +kernel
def cuts46082 : List PrefixCut := [⟨43,182883074,182883183⟩,
⟨64,273648356,273648514⟩]
theorem checked46082 : checkPrefixCuts (2^48) 6043992065 10 Manual.Count131072.C046082.packed 64 cuts46082 = true := by
 decide +kernel
def pointBounds46082 : List (Nat × Nat × Nat) := [(6044080128,110639693782823,110640080323187)]
theorem point_links_checked46082 : (cuts46082.take 1).map (fun c => (6043992065-1+2*2^10*c.k,110639510899749+c.lower,110639897440004+c.upper)) = pointBounds46082 := by
 decide +kernel
def cuts46083 : List PrefixCut := [⟨64,268007524,268007684⟩]
theorem checked46083 : checkPrefixCuts (2^48) 6044123137 10 Manual.Count131072.C046083.packed 64 cuts46083 = true := by
 decide +kernel
def cuts46084 : List PrefixCut := [⟨8,33110517,33110535⟩,
⟨64,267862011,267862163⟩]
theorem checked46084 : checkPrefixCuts (2^48) 6044254209 10 Manual.Count131072.C046084.packed 64 cuts46084 = true := by
 decide +kernel
def pointBounds46084 : List (Nat × Nat × Nat) := [(6044270592,110640085666146,110640472206737)]
theorem point_links_checked46084 : (cuts46084.take 1).map (fun c => (6044254209-1+2*2^10*c.k,110640052555629+c.lower,110640439096202+c.upper)) = pointBounds46084 := by
 decide +kernel
def cuts46085 : List PrefixCut := [⟨37,155396421,155396511⟩,
⟨64,268135605,268135761⟩]
theorem checked46085 : checkPrefixCuts (2^48) 6044385281 10 Manual.Count131072.C046085.packed 64 cuts46085 = true := by
 decide +kernel
def pointBounds46085 : List (Nat × Nat × Nat) := [(6044461056,110640475814061,110640862354876)]
theorem point_links_checked46085 : (cuts46085.take 1).map (fun c => (6044385281-1+2*2^10*c.k,110640320417640+c.lower,110640706958365+c.upper)) = pointBounds46085 := by
 decide +kernel
def cuts46086 : List PrefixCut := [⟨64,266965646,266965802⟩]
theorem checked46086 : checkPrefixCuts (2^48) 6044516353 10 Manual.Count131072.C046086.packed 64 cuts46086 = true := by
 decide +kernel
def cuts46087 : List PrefixCut := [⟨2,8987230,8987235⟩,
⟨64,269846883,269847040⟩]
theorem checked46087 : checkPrefixCuts (2^48) 6044647425 10 Manual.Count131072.C046087.packed 64 cuts46087 = true := by
 decide +kernel
def pointBounds46087 : List (Nat × Nat × Nat) := [(6044651520,110640864506121,110641251047163)]
theorem point_links_checked46087 : (cuts46087.take 1).map (fun c => (6044647425-1+2*2^10*c.k,110640855518891+c.lower,110641242059928+c.upper)) = pointBounds46087 := by
 decide +kernel
def cuts46088 : List PrefixCut := [⟨31,129729300,129729375⟩,
⟨64,270725735,270725892⟩]
theorem checked46088 : checkPrefixCuts (2^48) 6044778497 10 Manual.Count131072.C046088.packed 64 cuts46088 = true := by
 decide +kernel
def pointBounds46088 : List (Nat × Nat × Nat) := [(6044841984,110641255095074,110641641636343)]
theorem point_links_checked46088 : (cuts46088.take 1).map (fun c => (6044778497-1+2*2^10*c.k,110641125365774+c.lower,110641511906968+c.upper)) = pointBounds46088 := by
 decide +kernel
def cuts46089 : List PrefixCut := [⟨60,252141271,252141417⟩,
⟨64,269229884,269230038⟩]
theorem checked46089 : checkPrefixCuts (2^48) 6044909569 10 Manual.Count131072.C046089.packed 64 cuts46089 = true := by
 decide +kernel
def pointBounds46089 : List (Nat × Nat × Nat) := [(6045032448,110641648232780,110642034774277)]
theorem point_links_checked46089 : (cuts46089.take 1).map (fun c => (6044909569-1+2*2^10*c.k,110641396091509+c.lower,110641782632860+c.upper)) = pointBounds46089 := by
 decide +kernel
def cuts46090 : List PrefixCut := [⟨64,269503407,269503562⟩]
theorem checked46090 : checkPrefixCuts (2^48) 6045040641 10 Manual.Count131072.C046090.packed 64 cuts46090 = true := by
 decide +kernel
def cuts46091 : List PrefixCut := [⟨25,106626377,106626440⟩,
⟨64,270987529,270987688⟩]
theorem checked46091 : checkPrefixCuts (2^48) 6045171713 10 Manual.Count131072.C046091.packed 64 cuts46091 = true := by
 decide +kernel
def pointBounds46091 : List (Nat × Nat × Nat) := [(6045222912,110642041451177,110642427992900)]
theorem point_links_checked46091 : (cuts46091.take 1).map (fun c => (6045171713-1+2*2^10*c.k,110641934824800+c.lower,110642321366460+c.upper)) = pointBounds46091 := by
 decide +kernel
def cuts46092 : List PrefixCut := [⟨54,225632195,225632325⟩,
⟨64,269771073,269771226⟩]
theorem checked46092 : checkPrefixCuts (2^48) 6045302785 10 Manual.Count131072.C046092.packed 64 cuts46092 = true := by
 decide +kernel
def pointBounds46092 : List (Nat × Nat × Nat) := [(6045413376,110642431444524,110642817986473)]
theorem point_links_checked46092 : (cuts46092.take 1).map (fun c => (6045302785-1+2*2^10*c.k,110642205812329+c.lower,110642592354148+c.upper)) = pointBounds46092 := by
 decide +kernel
def cuts46093 : List PrefixCut := [⟨64,269998028,269998189⟩]
theorem checked46093 : checkPrefixCuts (2^48) 6045433857 10 Manual.Count131072.C046093.packed 64 cuts46093 = true := by
 decide +kernel
def cuts46094 : List PrefixCut := [⟨19,80965676,80965723⟩,
⟨64,274554884,274555046⟩]
theorem checked46094 : checkPrefixCuts (2^48) 6045564929 10 Manual.Count131072.C046094.packed 64 cuts46094 = true := by
 decide +kernel
def pointBounds46094 : List (Nat × Nat × Nat) := [(6045603840,110642826547106,110643213089286)]
theorem point_links_checked46094 : (cuts46094.take 1).map (fun c => (6045564929-1+2*2^10*c.k,110642745581430+c.lower,110643132123563+c.upper)) = pointBounds46094 := by
 decide +kernel
def cuts46095 : List PrefixCut := [⟨48,205132439,205132561⟩,
⟨64,273198794,273198957⟩]
theorem checked46095 : checkPrefixCuts (2^48) 6045696001 10 Manual.Count131072.C046095.packed 64 cuts46095 = true := by
 decide +kernel
def pointBounds46095 : List (Nat × Nat × Nat) := [(6045794304,110643225268753,110643611811170)]
theorem point_links_checked46095 : (cuts46095.take 1).map (fun c => (6045696001-1+2*2^10*c.k,110643020136314+c.lower,110643406678609+c.upper)) = pointBounds46095 := by
 decide +kernel
def cuts46096 : List PrefixCut := [⟨64,268769995,268770151⟩]
theorem checked46096 : checkPrefixCuts (2^48) 6045827073 10 Manual.Count131072.C046096.packed 64 cuts46096 = true := by
 decide +kernel
def cuts46097 : List PrefixCut := [⟨13,55168595,55168627⟩,
⟨64,271324716,271324874⟩]
theorem checked46097 : checkPrefixCuts (2^48) 6045958145 10 Manual.Count131072.C046097.packed 64 cuts46097 = true := by
 decide +kernel
def pointBounds46097 : List (Nat × Nat × Nat) := [(6045984768,110643617273698,110644003816344)]
theorem point_links_checked46097 : (cuts46097.take 1).map (fun c => (6045958145-1+2*2^10*c.k,110643562105103+c.lower,110643948647717+c.upper)) = pointBounds46097 := by
 decide +kernel
def cuts46098 : List PrefixCut := [⟨42,178722862,178722963⟩,
⟨64,269270461,269270613⟩]
theorem checked46098 : checkPrefixCuts (2^48) 6046089217 10 Manual.Count131072.C046098.packed 64 cuts46098 = true := by
 decide +kernel
def pointBounds46098 : List (Nat × Nat × Nat) := [(6046175232,110644012152681,110644398695554)]
theorem point_links_checked46098 : (cuts46098.take 1).map (fun c => (6046089217-1+2*2^10*c.k,110643833429819+c.lower,110644219972591+c.upper)) = pointBounds46098 := by
 decide +kernel
def cuts46099 : List PrefixCut := [⟨64,271685410,271685566⟩]
theorem checked46099 : checkPrefixCuts (2^48) 6046220289 10 Manual.Count131072.C046099.packed 64 cuts46099 = true := by
 decide +kernel
def cuts46100 : List PrefixCut := [⟨7,29886895,29886912⟩,
⟨64,266977731,266977889⟩]
theorem checked46100 : checkPrefixCuts (2^48) 6046351361 10 Manual.Count131072.C046100.packed 64 cuts46100 = true := by
 decide +kernel
def pointBounds46100 : List (Nat × Nat × Nat) := [(6046365696,110644404272585,110644790815682)]
theorem point_links_checked46100 : (cuts46100.take 1).map (fun c => (6046351361-1+2*2^10*c.k,110644374385690+c.lower,110644760928770+c.upper)) = pointBounds46100 := by
 decide +kernel
def cuts46101 : List PrefixCut := [⟨36,152409797,152409883⟩,
⟨64,270183973,270184127⟩]
theorem checked46101 : checkPrefixCuts (2^48) 6046482433 10 Manual.Count131072.C046101.packed 64 cuts46101 = true := by
 decide +kernel
def pointBounds46101 : List (Nat × Nat × Nat) := [(6046556160,110644793773218,110645180316542)]
theorem point_links_checked46101 : (cuts46101.take 1).map (fun c => (6046482433-1+2*2^10*c.k,110644641363421+c.lower,110645027906659+c.upper)) = pointBounds46101 := by
 decide +kernel
def cuts46102 : List PrefixCut := [⟨64,270829808,270829955⟩]
theorem checked46102 : checkPrefixCuts (2^48) 6046613505 10 Manual.Count131072.C046102.packed 64 cuts46102 = true := by
 decide +kernel
def cuts46103 : List PrefixCut := [⟨1,4236033,4236036⟩,
⟨64,271103217,271103381⟩]
theorem checked46103 : checkPrefixCuts (2^48) 6046744577 10 Manual.Count131072.C046103.packed 64 cuts46103 = true := by
 decide +kernel
def pointBounds46103 : List (Nat × Nat × Nat) := [(6046746624,110645186613235,110645573156777)]
theorem point_links_checked46103 : (cuts46103.take 1).map (fun c => (6046744577-1+2*2^10*c.k,110645182377202+c.lower,110645568920741+c.upper)) = pointBounds46103 := by
 decide +kernel
def cuts46104 : List PrefixCut := [⟨30,127915496,127915568⟩,
⟨64,267885550,267885705⟩]
theorem checked46104 : checkPrefixCuts (2^48) 6046875649 10 Manual.Count131072.C046104.packed 64 cuts46104 = true := by
 decide +kernel
def pointBounds46104 : List (Nat × Nat × Nat) := [(6046937088,110645581395915,110645967939690)]
theorem point_links_checked46104 : (cuts46104.take 1).map (fun c => (6046875649-1+2*2^10*c.k,110645453480419+c.lower,110645840024122+c.upper)) = pointBounds46104 := by
 decide +kernel
def cuts46105 : List PrefixCut := [⟨59,249866127,249866271⟩,
⟨64,270160549,270160703⟩]
theorem checked46105 : checkPrefixCuts (2^48) 6047006721 10 Manual.Count131072.C046105.packed 64 cuts46105 = true := by
 decide +kernel
def pointBounds46105 : List (Nat × Nat × Nat) := [(6047127552,110645971232096,110646357776098)]
theorem point_links_checked46105 : (cuts46105.take 1).map (fun c => (6047006721-1+2*2^10*c.k,110645721365969+c.lower,110646107909827+c.upper)) = pointBounds46105 := by
 decide +kernel
def cuts46106 : List PrefixCut := [⟨64,268432456,268432605⟩]
theorem checked46106 : checkPrefixCuts (2^48) 6047137793 10 Manual.Count131072.C046106.packed 64 cuts46106 = true := by
 decide +kernel
def cuts46107 : List PrefixCut := [⟨24,101143581,101143643⟩,
⟨64,269590271,269590433⟩]
theorem checked46107 : checkPrefixCuts (2^48) 6047268865 10 Manual.Count131072.C046107.packed 64 cuts46107 = true := by
 decide +kernel
def pointBounds46107 : List (Nat × Nat × Nat) := [(6047318016,110646361102555,110646747646778)]
theorem point_links_checked46107 : (cuts46107.take 1).map (fun c => (6047268865-1+2*2^10*c.k,110646259958974+c.lower,110646646503135+c.upper)) = pointBounds46107 := by
 decide +kernel
def cuts46108 : List PrefixCut := [⟨53,223412931,223413061⟩,
⟨64,268886279,268886436⟩]
theorem checked46108 : checkPrefixCuts (2^48) 6047399937 10 Manual.Count131072.C046108.packed 64 cuts46108 = true := by
 decide +kernel
def pointBounds46108 : List (Nat × Nat × Nat) := [(6047508480,110646752962176,110647139506629)]
theorem point_links_checked46108 : (cuts46108.take 1).map (fun c => (6047399937-1+2*2^10*c.k,110646529549245+c.lower,110646916093568+c.upper)) = pointBounds46108 := by
 decide +kernel
def cuts46109 : List PrefixCut := [⟨64,268647748,268647900⟩]
theorem checked46109 : checkPrefixCuts (2^48) 6047531009 10 Manual.Count131072.C046109.packed 64 cuts46109 = true := by
 decide +kernel
def cuts46110 : List PrefixCut := [⟨18,78610488,78610531⟩,
⟨64,272784202,272784359⟩]
theorem checked46110 : checkPrefixCuts (2^48) 6047662081 10 Manual.Count131072.C046110.packed 64 cuts46110 = true := by
 decide +kernel
def pointBounds46110 : List (Nat × Nat × Nat) := [(6047698944,110647145693760,110647532238435)]
theorem point_links_checked46110 : (cuts46110.take 1).map (fun c => (6047662081-1+2*2^10*c.k,110647067083272+c.lower,110647453627904+c.upper)) = pointBounds46110 := by
 decide +kernel
def cuts46111 : List PrefixCut := [⟨47,199429830,199429948⟩,
⟨64,270963161,270963319⟩]
theorem checked46111 : checkPrefixCuts (2^48) 6047793153 10 Manual.Count131072.C046111.packed 64 cuts46111 = true := by
 decide +kernel
def pointBounds46111 : List (Nat × Nat × Nat) := [(6047889408,110647539297304,110647925842211)]
theorem point_links_checked46111 : (cuts46111.take 1).map (fun c => (6047793153-1+2*2^10*c.k,110647339867474+c.lower,110647726412263+c.upper)) = pointBounds46111 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S5.B000190
