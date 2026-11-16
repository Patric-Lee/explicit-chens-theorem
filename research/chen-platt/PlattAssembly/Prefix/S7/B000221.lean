import PlattAssemblyKernel
import PlattCertificates.Count131072.C067072
import PlattCertificates.Count131072.C067073
import PlattCertificates.Count131072.C067074
import PlattCertificates.Count131072.C067075
import PlattCertificates.Count131072.C067076
import PlattCertificates.Count131072.C067077
import PlattCertificates.Count131072.C067078
import PlattCertificates.Count131072.C067079
import PlattCertificates.Count131072.C067080
import PlattCertificates.Count131072.C067081
import PlattCertificates.Count131072.C067082
import PlattCertificates.Count131072.C067083
import PlattCertificates.Count131072.C067084
import PlattCertificates.Count131072.C067085
import PlattCertificates.Count131072.C067086
import PlattCertificates.Count131072.C067087
import PlattCertificates.Count131072.C067088
import PlattCertificates.Count131072.C067089
import PlattCertificates.Count131072.C067090
import PlattCertificates.Count131072.C067091
import PlattCertificates.Count131072.C067092
import PlattCertificates.Count131072.C067093
import PlattCertificates.Count131072.C067094
import PlattCertificates.Count131072.C067095
import PlattCertificates.Count131072.C067096
import PlattCertificates.Count131072.C067097
import PlattCertificates.Count131072.C067098
import PlattCertificates.Count131072.C067099
import PlattCertificates.Count131072.C067100
import PlattCertificates.Count131072.C067101
import PlattCertificates.Count131072.C067102
import PlattCertificates.Count131072.C067103
namespace ChenEffective.PlattWindow.Assembly.Prefix.S7.B000221
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts67072 : List PrefixCut := [⟨64,183441342,183441448⟩]
theorem checked67072 : checkPrefixCuts (2^48) 8795193345 10 Manual.Count131072.C067072.packed 64 cuts67072 = true := by
 decide +kernel
def cuts67073 : List PrefixCut := [⟨26,72902126,72902169⟩,
⟨64,183214578,183214684⟩]
theorem checked67073 : checkPrefixCuts (2^48) 8795324417 10 Manual.Count131072.C067073.packed 64 cuts67073 = true := by
 decide +kernel
def pointBounds67073 : List (Nat × Nat × Nat) := [(8795377664,115289473970543,115289863168711)]
theorem point_links_checked67073 : (cuts67073.take 1).map (fun c => (8795324417-1+2*2^10*c.k,115289401068417+c.lower,115289790266542+c.upper)) = pointBounds67073 := by
 decide +kernel
def cuts67074 : List PrefixCut := [⟨64,181739775,181739877⟩]
theorem checked67074 : checkPrefixCuts (2^48) 8795455489 10 Manual.Count131072.C067074.packed 64 cuts67074 = true := by
 decide +kernel
def cuts67075 : List PrefixCut := [⟨33,96677166,96677221⟩,
⟨64,184329199,184329309⟩]
theorem checked67075 : checkPrefixCuts (2^48) 8795586561 10 Manual.Count131072.C067075.packed 64 cuts67075 = true := by
 decide +kernel
def pointBounds67075 : List (Nat × Nat × Nat) := [(8795654144,115289862699936,115290251898324)]
theorem point_links_checked67075 : (cuts67075.take 1).map (fun c => (8795586561-1+2*2^10*c.k,115289766022770+c.lower,115290155221103+c.upper)) = pointBounds67075 := by
 decide +kernel
def cuts67076 : List PrefixCut := [⟨64,184422433,184422541⟩]
theorem checked67076 : checkPrefixCuts (2^48) 8795717633 10 Manual.Count131072.C067076.packed 64 cuts67076 = true := by
 decide +kernel
def cuts67077 : List PrefixCut := [⟨40,117666682,117666751⟩,
⟨64,185443722,185443833⟩]
theorem checked67077 : checkPrefixCuts (2^48) 8795848705 10 Manual.Count131072.C067077.packed 64 cuts67077 = true := by
 decide +kernel
def pointBounds67077 : List (Nat × Nat × Nat) := [(8795930624,115290252441084,115290641639704)]
theorem point_links_checked67077 : (cuts67077.take 1).map (fun c => (8795848705-1+2*2^10*c.k,115290134774402+c.lower,115290523972953+c.upper)) = pointBounds67077 := by
 decide +kernel
def cuts67078 : List PrefixCut := [⟨64,184768948,184769062⟩]
theorem checked67078 : checkPrefixCuts (2^48) 8795979777 10 Manual.Count131072.C067078.packed 64 cuts67078 = true := by
 decide +kernel
def cuts67079 : List PrefixCut := [⟨47,132446963,132447040⟩,
⟨64,181470216,181470324⟩]
theorem checked67079 : checkPrefixCuts (2^48) 8796110849 10 Manual.Count131072.C067079.packed 64 cuts67079 = true := by
 decide +kernel
def pointBounds67079 : List (Nat × Nat × Nat) := [(8796207104,115290637434035,115291026632888)]
theorem point_links_checked67079 : (cuts67079.take 1).map (fun c => (8796110849-1+2*2^10*c.k,115290504987072+c.lower,115290894185848+c.upper)) = pointBounds67079 := by
 decide +kernel
def cuts67080 : List PrefixCut := [⟨64,181115545,181115651⟩]
theorem checked67080 : checkPrefixCuts (2^48) 8796241921 10 Manual.Count131072.C067080.packed 64 cuts67080 = true := by
 decide +kernel
def cuts67081 : List PrefixCut := [⟨54,154074090,154074173⟩,
⟨64,183160756,183160857⟩]
theorem checked67081 : checkPrefixCuts (2^48) 8796372993 10 Manual.Count131072.C067081.packed 64 cuts67081 = true := by
 decide +kernel
def pointBounds67081 : List (Nat × Nat × Nat) := [(8796483584,115291021646923,115291410845996)]
theorem point_links_checked67081 : (cuts67081.take 1).map (fun c => (8796372993-1+2*2^10*c.k,115290867572833+c.lower,115291256771823+c.upper)) = pointBounds67081 := by
 decide +kernel
def cuts67082 : List PrefixCut := [⟨64,183478015,183478118⟩]
theorem checked67082 : checkPrefixCuts (2^48) 8796504065 10 Manual.Count131072.C067082.packed 64 cuts67082 = true := by
 decide +kernel
def cuts67083 : List PrefixCut := [⟨61,175187900,175188003⟩,
⟨64,183187287,183187396⟩]
theorem checked67083 : checkPrefixCuts (2^48) 8796635137 10 Manual.Count131072.C067083.packed 64 cuts67083 = true := by
 decide +kernel
def pointBounds67083 : List (Nat × Nat × Nat) := [(8796760064,115291409399504,115291798598801)]
theorem point_links_checked67083 : (cuts67083.take 1).map (fun c => (8796635137-1+2*2^10*c.k,115291234211604+c.lower,115291623410798+c.upper)) = pointBounds67083 := by
 decide +kernel
def cuts67084 : List PrefixCut := [⟨64,183824514,183824622⟩]
theorem checked67084 : checkPrefixCuts (2^48) 8796766209 10 Manual.Count131072.C067084.packed 64 cuts67084 = true := by
 decide +kernel
def cuts67085 : List PrefixCut := [⟨64,184525700,184525808⟩]
theorem checked67085 : checkPrefixCuts (2^48) 8796897281 10 Manual.Count131072.C067085.packed 64 cuts67085 = true := by
 decide +kernel
def cuts67086 : List PrefixCut := [⟨4,11134808,11134814⟩,
⟨64,183339075,183339184⟩]
theorem checked67086 : checkPrefixCuts (2^48) 8797028353 10 Manual.Count131072.C067086.packed 64 cuts67086 = true := by
 decide +kernel
def pointBounds67086 : List (Nat × Nat × Nat) := [(8797036544,115291796883913,115292186083438)]
theorem point_links_checked67086 : (cuts67086.take 1).map (fun c => (8797028353-1+2*2^10*c.k,115291785749105+c.lower,115292174948624+c.upper)) = pointBounds67086 := by
 decide +kernel
def cuts67087 : List PrefixCut := [⟨64,184904156,184904257⟩]
theorem checked67087 : checkPrefixCuts (2^48) 8797159425 10 Manual.Count131072.C067087.packed 64 cuts67087 = true := by
 decide +kernel
def cuts67088 : List PrefixCut := [⟨11,31643642,31643659⟩,
⟨64,183717562,183717663⟩]
theorem checked67088 : checkPrefixCuts (2^48) 8797290497 10 Manual.Count131072.C067088.packed 64 cuts67088 = true := by
 decide +kernel
def pointBounds67088 : List (Nat × Nat × Nat) := [(8797313024,115292185635978,115292574835724)]
theorem point_links_checked67088 : (cuts67088.take 1).map (fun c => (8797290497-1+2*2^10*c.k,115292153992336+c.lower,115292543192065+c.upper)) = pointBounds67088 := by
 decide +kernel
def cuts67089 : List PrefixCut := [⟨64,183042927,183043035⟩]
theorem checked67089 : checkPrefixCuts (2^48) 8797421569 10 Manual.Count131072.C067089.packed 64 cuts67089 = true := by
 decide +kernel
def cuts67090 : List PrefixCut := [⟨18,50007581,50007614⟩,
⟨64,182656261,182656370⟩]
theorem checked67090 : checkPrefixCuts (2^48) 8797552641 10 Manual.Count131072.C067090.packed 64 cuts67090 = true := by
 decide +kernel
def pointBounds67090 : List (Nat × Nat × Nat) := [(8797589504,115292570760406,115292959960377)]
theorem point_links_checked67090 : (cuts67090.take 1).map (fun c => (8797552641-1+2*2^10*c.k,115292520752825+c.lower,115292909952763+c.upper)) = pointBounds67090 := by
 decide +kernel
def cuts67091 : List PrefixCut := [⟨64,181277799,181277911⟩]
theorem checked67091 : checkPrefixCuts (2^48) 8797683713 10 Manual.Count131072.C067091.packed 64 cuts67091 = true := by
 decide +kernel
def cuts67092 : List PrefixCut := [⟨25,73137448,73137488⟩,
⟨64,184122547,184122647⟩]
theorem checked67092 : checkPrefixCuts (2^48) 8797814785 10 Manual.Count131072.C067092.packed 64 cuts67092 = true := by
 decide +kernel
def pointBounds67092 : List (Nat × Nat × Nat) := [(8797865984,115292957824333,115293347024532)]
theorem point_links_checked67092 : (cuts67092.take 1).map (fun c => (8797814785-1+2*2^10*c.k,115292884686885+c.lower,115293273887044+c.upper)) = pointBounds67092 := by
 decide +kernel
def cuts67093 : List PrefixCut := [⟨64,183064024,183064125⟩]
theorem checked67093 : checkPrefixCuts (2^48) 8797945857 10 Manual.Count131072.C067093.packed 64 cuts67093 = true := by
 decide +kernel
def cuts67094 : List PrefixCut := [⟨32,91179065,91179120⟩,
⟨64,185236769,185236882⟩]
theorem checked67094 : checkPrefixCuts (2^48) 8798076929 10 Manual.Count131072.C067094.packed 64 cuts67094 = true := by
 decide +kernel
def pointBounds67094 : List (Nat × Nat × Nat) := [(8798142464,115293343052521,115293732252936)]
theorem point_links_checked67094 : (cuts67094.take 1).map (fun c => (8798076929-1+2*2^10*c.k,115293251873456+c.lower,115293641073816+c.upper)) = pointBounds67094 := by
 decide +kernel
def cuts67095 : List PrefixCut := [⟨64,181554930,181555040⟩]
theorem checked67095 : checkPrefixCuts (2^48) 8798208001 10 Manual.Count131072.C067095.packed 64 cuts67095 = true := by
 decide +kernel
def cuts67096 : List PrefixCut := [⟨39,111363022,111363086⟩,
⟨64,181712191,181712294⟩]
theorem checked67096 : checkPrefixCuts (2^48) 8798339073 10 Manual.Count131072.C067096.packed 64 cuts67096 = true := by
 decide +kernel
def pointBounds67096 : List (Nat × Nat × Nat) := [(8798418944,115293730028177,115294119228824)]
theorem point_links_checked67096 : (cuts67096.take 1).map (fun c => (8798339073-1+2*2^10*c.k,115293618665155+c.lower,115294007865738+c.upper)) = pointBounds67096 := by
 decide +kernel
def cuts67097 : List PrefixCut := [⟨64,182701199,182701307⟩]
theorem checked67097 : checkPrefixCuts (2^48) 8798470145 10 Manual.Count131072.C067097.packed 64 cuts67097 = true := by
 decide +kernel
def cuts67098 : List PrefixCut := [⟨46,130234128,130234202⟩,
⟨64,181418861,181418963⟩]
theorem checked67098 : checkPrefixCuts (2^48) 8798601217 10 Manual.Count131072.C067098.packed 64 cuts67098 = true := by
 decide +kernel
def pointBounds67098 : List (Nat × Nat × Nat) := [(8798695424,115294113312673,115294502513541)]
theorem point_links_checked67098 : (cuts67098.take 1).map (fun c => (8798601217-1+2*2^10*c.k,115293983078545+c.lower,115294372279339+c.upper)) = pointBounds67098 := by
 decide +kernel
def cuts67099 : List PrefixCut := [⟨64,184775135,184775230⟩]
theorem checked67099 : checkPrefixCuts (2^48) 8798732289 10 Manual.Count131072.C067099.packed 64 cuts67099 = true := by
 decide +kernel
def cuts67100 : List PrefixCut := [⟨53,151055454,151055540⟩,
⟨64,183204881,183204986⟩]
theorem checked67100 : checkPrefixCuts (2^48) 8798863361 10 Manual.Count131072.C067100.packed 64 cuts67100 = true := by
 decide +kernel
def pointBounds67100 : List (Nat × Nat × Nat) := [(8798971904,115294500327995,115294889529072)]
theorem point_links_checked67100 : (cuts67100.take 1).map (fun c => (8798863361-1+2*2^10*c.k,115294349272541+c.lower,115294738473532+c.upper)) = pointBounds67100 := by
 decide +kernel
def cuts67101 : List PrefixCut := [⟨64,181282800,181282907⟩]
theorem checked67101 : checkPrefixCuts (2^48) 8798994433 10 Manual.Count131072.C067101.packed 64 cuts67101 = true := by
 decide +kernel
def cuts67102 : List PrefixCut := [⟨60,172611238,172611343⟩,
⟨64,184191075,184191187⟩]
theorem checked67102 : checkPrefixCuts (2^48) 8799125505 10 Manual.Count131072.C067102.packed 64 cuts67102 = true := by
 decide +kernel
def pointBounds67102 : List (Nat × Nat × Nat) := [(8799248384,115294886371460,115295275572768)]
theorem point_links_checked67102 : (cuts67102.take 1).map (fun c => (8799125505-1+2*2^10*c.k,115294713760222+c.lower,115295102961425+c.upper)) = pointBounds67102 := by
 decide +kernel
def cuts67103 : List PrefixCut := [⟨64,183100729,183100835⟩]
theorem checked67103 : checkPrefixCuts (2^48) 8799256577 10 Manual.Count131072.C067103.packed 64 cuts67103 = true := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S7.B000221
