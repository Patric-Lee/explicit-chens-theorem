import PlattAssemblyKernel
import PlattCertificates.Count131072.C071120
import PlattCertificates.Count131072.C071121
import PlattCertificates.Count131072.C071122
import PlattCertificates.Count131072.C071123
import PlattCertificates.Count131072.C071124
import PlattCertificates.Count131072.C071125
import PlattCertificates.Count131072.C071126
import PlattCertificates.Count131072.C071127
import PlattCertificates.Count131072.C071128
import PlattCertificates.Count131072.C071129
import PlattCertificates.Count131072.C071130
import PlattCertificates.Count131072.C071131
import PlattCertificates.Count131072.C071132
import PlattCertificates.Count131072.C071133
import PlattCertificates.Count131072.C071134
import PlattCertificates.Count131072.C071135
import PlattCertificates.Count131072.C071136
import PlattCertificates.Count131072.C071137
import PlattCertificates.Count131072.C071138
import PlattCertificates.Count131072.C071139
import PlattCertificates.Count131072.C071140
import PlattCertificates.Count131072.C071141
import PlattCertificates.Count131072.C071142
import PlattCertificates.Count131072.C071143
import PlattCertificates.Count131072.C071144
import PlattCertificates.Count131072.C071145
import PlattCertificates.Count131072.C071146
import PlattCertificates.Count131072.C071147
import PlattCertificates.Count131072.C071148
import PlattCertificates.Count131072.C071149
import PlattCertificates.Count131072.C071150
import PlattCertificates.Count131072.C071151
namespace ChenEffective.PlattWindow.Assembly.Prefix.S8.B000035
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts71120 : List PrefixCut := [⟨64,173095280,173095377⟩]
theorem checked71120 : checkPrefixCuts (2^48) 9325772801 10 Manual.Count131072.C071120.packed 64 cuts71120 = true := by
 decide +kernel
def cuts71121 : List PrefixCut := [⟨64,171734657,171734757⟩]
theorem checked71121 : checkPrefixCuts (2^48) 9325903873 10 Manual.Count131072.C071121.packed 64 cuts71121 = true := by
 decide +kernel
def cuts71122 : List PrefixCut := [⟨10,27857610,27857628⟩,
⟨64,173060224,173060328⟩]
theorem checked71122 : checkPrefixCuts (2^48) 9326034945 10 Manual.Count131072.C071122.packed 64 cuts71122 = true := by
 decide +kernel
def pointBounds71122 : List (Nat × Nat × Nat) := [(9326055424,116008761183542,116009150803743)]
theorem point_links_checked71122 : (cuts71122.take 1).map (fun c => (9326034945-1+2*2^10*c.k,116008733325932+c.lower,116009122946115+c.upper)) = pointBounds71122 := by
 decide +kernel
def cuts71123 : List PrefixCut := [⟨64,171246924,171247027⟩]
theorem checked71123 : checkPrefixCuts (2^48) 9326166017 10 Manual.Count131072.C071123.packed 64 cuts71123 = true := by
 decide +kernel
def cuts71124 : List PrefixCut := [⟨25,65099755,65099793⟩,
⟨64,172512095,172512197⟩]
theorem checked71124 : checkPrefixCuts (2^48) 9326297089 10 Manual.Count131072.C071124.packed 64 cuts71124 = true := by
 decide +kernel
def pointBounds71124 : List (Nat × Nat × Nat) := [(9326348288,116009142732835,116009532353263)]
theorem point_links_checked71124 : (cuts71124.take 1).map (fun c => (9326297089-1+2*2^10*c.k,116009077633080+c.lower,116009467253470+c.upper)) = pointBounds71124 := by
 decide +kernel
def cuts71125 : List PrefixCut := [⟨64,171996605,171996705⟩]
theorem checked71125 : checkPrefixCuts (2^48) 9326428161 10 Manual.Count131072.C071125.packed 64 cuts71125 = true := by
 decide +kernel
def cuts71126 : List PrefixCut := [⟨40,108918882,108918944⟩,
⟨64,171541521,171541618⟩]
theorem checked71126 : checkPrefixCuts (2^48) 9326559233 10 Manual.Count131072.C071126.packed 64 cuts71126 = true := by
 decide +kernel
def pointBounds71126 : List (Nat × Nat × Nat) := [(9326641152,116009531060662,116009920681316)]
theorem point_links_checked71126 : (cuts71126.take 1).map (fun c => (9326559233-1+2*2^10*c.k,116009422141780+c.lower,116009811762372+c.upper)) = pointBounds71126 := by
 decide +kernel
def cuts71127 : List PrefixCut := [⟨64,173108417,173108524⟩]
theorem checked71127 : checkPrefixCuts (2^48) 9326690305 10 Manual.Count131072.C071127.packed 64 cuts71127 = true := by
 decide +kernel
def cuts71128 : List PrefixCut := [⟨55,149506267,149506349⟩,
⟨64,174433862,174433959⟩]
theorem checked71128 : checkPrefixCuts (2^48) 9326821377 10 Manual.Count131072.C071128.packed 64 cuts71128 = true := by
 decide +kernel
def pointBounds71128 : List (Nat × Nat × Nat) := [(9326934016,116009916297985,116010305918863)]
theorem point_links_checked71128 : (cuts71128.take 1).map (fun c => (9326821377-1+2*2^10*c.k,116009766791718+c.lower,116010156412514+c.upper)) = pointBounds71128 := by
 decide +kernel
def cuts71129 : List PrefixCut := [⟨64,170930725,170930828⟩]
theorem checked71129 : checkPrefixCuts (2^48) 9326952449 10 Manual.Count131072.C071129.packed 64 cuts71129 = true := by
 decide +kernel
def cuts71130 : List PrefixCut := [⟨64,173976280,173976381⟩]
theorem checked71130 : checkPrefixCuts (2^48) 9327083521 10 Manual.Count131072.C071130.packed 64 cuts71130 = true := by
 decide +kernel
def cuts71131 : List PrefixCut := [⟨6,16024405,16024416⟩,
⟨64,172796913,172797015⟩]
theorem checked71131 : checkPrefixCuts (2^48) 9327214593 10 Manual.Count131072.C071131.packed 64 cuts71131 = true := by
 decide +kernel
def pointBounds71131 : List (Nat × Nat × Nat) := [(9327226880,116010302156990,116010691778098)]
theorem point_links_checked71131 : (cuts71131.take 1).map (fun c => (9327214593-1+2*2^10*c.k,116010286132585+c.lower,116010675753682+c.upper)) = pointBounds71131 := by
 decide +kernel
def cuts71132 : List PrefixCut := [⟨64,170199245,170199340⟩]
theorem checked71132 : checkPrefixCuts (2^48) 9327345665 10 Manual.Count131072.C071132.packed 64 cuts71132 = true := by
 decide +kernel
def cuts71133 : List PrefixCut := [⟨21,56551494,56551523⟩,
⟨64,169683853,169683947⟩]
theorem checked71133 : checkPrefixCuts (2^48) 9327476737 10 Manual.Count131072.C071133.packed 64 cuts71133 = true := by
 decide +kernel
def pointBounds71133 : List (Nat × Nat × Nat) := [(9327519744,116010685680237,116011075301560)]
theorem point_links_checked71133 : (cuts71133.take 1).map (fun c => (9327476737-1+2*2^10*c.k,116010629128743+c.lower,116011018750037+c.upper)) = pointBounds71133 := by
 decide +kernel
def cuts71134 : List PrefixCut := [⟨64,172005052,172005158⟩]
theorem checked71134 : checkPrefixCuts (2^48) 9327607809 10 Manual.Count131072.C071134.packed 64 cuts71134 = true := by
 decide +kernel
def cuts71135 : List PrefixCut := [⟨36,97015818,97015876⟩,
⟨64,170795604,170795702⟩]
theorem checked71135 : checkPrefixCuts (2^48) 9327738881 10 Manual.Count131072.C071135.packed 64 cuts71135 = true := by
 decide +kernel
def pointBounds71135 : List (Nat × Nat × Nat) := [(9327812608,116011067833466,116011457455018)]
theorem point_links_checked71135 : (cuts71135.take 1).map (fun c => (9327738881-1+2*2^10*c.k,116010970817648+c.lower,116011360439142+c.upper)) = pointBounds71135 := by
 decide +kernel
def cuts71136 : List PrefixCut := [⟨64,172392500,172392600⟩]
theorem checked71136 : checkPrefixCuts (2^48) 9327869953 10 Manual.Count131072.C071136.packed 64 cuts71136 = true := by
 decide +kernel
def cuts71137 : List PrefixCut := [⟨51,136331082,136331170⟩,
⟨64,170760623,170760732⟩]
theorem checked71137 : checkPrefixCuts (2^48) 9328001025 10 Manual.Count131072.C071137.packed 64 cuts71137 = true := by
 decide +kernel
def pointBounds71137 : List (Nat × Nat × Nat) := [(9328105472,116011450336834,116011839958614)]
theorem point_links_checked71137 : (cuts71137.take 1).map (fun c => (9328001025-1+2*2^10*c.k,116011314005752+c.lower,116011703627444+c.upper)) = pointBounds71137 := by
 decide +kernel
def cuts71138 : List PrefixCut := [⟨64,171361719,171361817⟩]
theorem checked71138 : checkPrefixCuts (2^48) 9328132097 10 Manual.Count131072.C071138.packed 64 cuts71138 = true := by
 decide +kernel
def cuts71139 : List PrefixCut := [⟨64,172505922,172506028⟩]
theorem checked71139 : checkPrefixCuts (2^48) 9328263169 10 Manual.Count131072.C071139.packed 64 cuts71139 = true := by
 decide +kernel
def cuts71140 : List PrefixCut := [⟨2,5521839,5521843⟩,
⟨64,171628454,171628565⟩]
theorem checked71140 : checkPrefixCuts (2^48) 9328394241 10 Manual.Count131072.C071140.packed 64 cuts71140 = true := by
 decide +kernel
def pointBounds71140 : List (Nat × Nat × Nat) := [(9328398336,116011834155855,116012223777864)]
theorem point_links_checked71140 : (cuts71140.take 1).map (fun c => (9328394241-1+2*2^10*c.k,116011828634016+c.lower,116012218256021+c.upper)) = pointBounds71140 := by
 decide +kernel
def cuts71141 : List PrefixCut := [⟨64,173677848,173677949⟩]
theorem checked71141 : checkPrefixCuts (2^48) 9328525313 10 Manual.Count131072.C071141.packed 64 cuts71141 = true := by
 decide +kernel
def cuts71142 : List PrefixCut := [⟨17,46768285,46768314⟩,
⟨64,173916779,173916884⟩]
theorem checked71142 : checkPrefixCuts (2^48) 9328656385 10 Manual.Count131072.C071142.packed 64 cuts71142 = true := by
 decide +kernel
def pointBounds71142 : List (Nat × Nat × Nat) := [(9328691200,116012220708603,116012610330849)]
theorem point_links_checked71142 : (cuts71142.take 1).map (fun c => (9328656385-1+2*2^10*c.k,116012173940318+c.lower,116012563562535+c.upper)) = pointBounds71142 := by
 decide +kernel
def cuts71143 : List PrefixCut := [⟨64,173672955,173673053⟩]
theorem checked71143 : checkPrefixCuts (2^48) 9328787457 10 Manual.Count131072.C071143.packed 64 cuts71143 = true := by
 decide +kernel
def cuts71144 : List PrefixCut := [⟨32,85930402,85930452⟩,
⟨64,171407619,171407720⟩]
theorem checked71144 : checkPrefixCuts (2^48) 9328918529 10 Manual.Count131072.C071144.packed 64 cuts71144 = true := by
 decide +kernel
def pointBounds71144 : List (Nat × Nat × Nat) := [(9328984064,116012607460454,116012997082924)]
theorem point_links_checked71144 : (cuts71144.take 1).map (fun c => (9328918529-1+2*2^10*c.k,116012521530052+c.lower,116012911152472+c.upper)) = pointBounds71144 := by
 decide +kernel
def cuts71145 : List PrefixCut := [⟨64,175327523,175327625⟩]
theorem checked71145 : checkPrefixCuts (2^48) 9329049601 10 Manual.Count131072.C071145.packed 64 cuts71145 = true := by
 decide +kernel
def cuts71146 : List PrefixCut := [⟨47,126357376,126357452⟩,
⟨64,172458789,172458890⟩]
theorem checked71146 : checkPrefixCuts (2^48) 9329180673 10 Manual.Count131072.C071146.packed 64 cuts71146 = true := by
 decide +kernel
def pointBounds71146 : List (Nat × Nat × Nat) := [(9329276928,116012994622570,116013384245269)]
theorem point_links_checked71146 : (cuts71146.take 1).map (fun c => (9329180673-1+2*2^10*c.k,116012868265194+c.lower,116013257887817+c.upper)) = pointBounds71146 := by
 decide +kernel
def cuts71147 : List PrefixCut := [⟨64,173663199,173663298⟩]
theorem checked71147 : checkPrefixCuts (2^48) 9329311745 10 Manual.Count131072.C071147.packed 64 cuts71147 = true := by
 decide +kernel
def cuts71148 : List PrefixCut := [⟨62,167385356,167385459⟩,
⟨64,172755649,172755755⟩]
theorem checked71148 : checkPrefixCuts (2^48) 9329442817 10 Manual.Count131072.C071148.packed 64 cuts71148 = true := by
 decide +kernel
def pointBounds71148 : List (Nat × Nat × Nat) := [(9329569792,116013381772538,116013771395464)]
theorem point_links_checked71148 : (cuts71148.take 1).map (fun c => (9329442817-1+2*2^10*c.k,116013214387182+c.lower,116013604010005+c.upper)) = pointBounds71148 := by
 decide +kernel
def cuts71149 : List PrefixCut := [⟨64,173266098,173266203⟩]
theorem checked71149 : checkPrefixCuts (2^48) 9329573889 10 Manual.Count131072.C071149.packed 64 cuts71149 = true := by
 decide +kernel
def cuts71150 : List PrefixCut := [⟨64,170065699,170065803⟩]
theorem checked71150 : checkPrefixCuts (2^48) 9329704961 10 Manual.Count131072.C071150.packed 64 cuts71150 = true := by
 decide +kernel
def cuts71151 : List PrefixCut := [⟨13,35509249,35509270⟩,
⟨64,173321585,173321686⟩]
theorem checked71151 : checkPrefixCuts (2^48) 9329836033 10 Manual.Count131072.C071151.packed 64 cuts71151 = true := by
 decide +kernel
def pointBounds71151 : List (Nat × Nat × Nat) := [(9329862656,116013765983877,116014155607036)]
theorem point_links_checked71151 : (cuts71151.take 1).map (fun c => (9329836033-1+2*2^10*c.k,116013730474628+c.lower,116014120097766+c.upper)) = pointBounds71151 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S8.B000035
