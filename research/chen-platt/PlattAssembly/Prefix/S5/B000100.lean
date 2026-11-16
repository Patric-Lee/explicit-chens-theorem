import PlattAssemblyKernel
import PlattCertificates.Count131072.C043200
import PlattCertificates.Count131072.C043201
import PlattCertificates.Count131072.C043202
import PlattCertificates.Count131072.C043203
import PlattCertificates.Count131072.C043204
import PlattCertificates.Count131072.C043205
import PlattCertificates.Count131072.C043206
import PlattCertificates.Count131072.C043207
import PlattCertificates.Count131072.C043208
import PlattCertificates.Count131072.C043209
import PlattCertificates.Count131072.C043210
import PlattCertificates.Count131072.C043211
import PlattCertificates.Count131072.C043212
import PlattCertificates.Count131072.C043213
import PlattCertificates.Count131072.C043214
import PlattCertificates.Count131072.C043215
import PlattCertificates.Count131072.C043216
import PlattCertificates.Count131072.C043217
import PlattCertificates.Count131072.C043218
import PlattCertificates.Count131072.C043219
import PlattCertificates.Count131072.C043220
import PlattCertificates.Count131072.C043221
import PlattCertificates.Count131072.C043222
import PlattCertificates.Count131072.C043223
import PlattCertificates.Count131072.C043224
import PlattCertificates.Count131072.C043225
import PlattCertificates.Count131072.C043226
import PlattCertificates.Count131072.C043227
import PlattCertificates.Count131072.C043228
import PlattCertificates.Count131072.C043229
import PlattCertificates.Count131072.C043230
import PlattCertificates.Count131072.C043231
namespace ChenEffective.PlattWindow.Assembly.Prefix.S5.B000100
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts43200 : List PrefixCut := [⟨37,167257170,167257264⟩,
⟨64,289904378,289904544⟩]
theorem checked43200 : checkPrefixCuts (2^48) 5666242561 10 Manual.Count131072.C043200.packed 64 cuts43200 = true := by
 decide +kernel
def pointBounds43200 : List (Nat × Nat × Nat) := [(5666318336,109831966860429,109832352933827)]
theorem point_links_checked43200 : (cuts43200.take 1).map (fun c => (5666242561-1+2*2^10*c.k,109831799603259+c.lower,109832185676563+c.upper)) = pointBounds43200 := by
 decide +kernel
def cuts43201 : List PrefixCut := [⟨60,271568148,271568301⟩,
⟨64,289450606,289450768⟩]
theorem checked43201 : checkPrefixCuts (2^48) 5666373633 10 Manual.Count131072.C043201.packed 64 cuts43201 = true := by
 decide +kernel
def pointBounds43201 : List (Nat × Nat × Nat) := [(5666496512,109832361075785,109832747149408)]
theorem point_links_checked43201 : (cuts43201.take 1).map (fun c => (5666373633-1+2*2^10*c.k,109832089507637+c.lower,109832475581107+c.upper)) = pointBounds43201 := by
 decide +kernel
def cuts43202 : List PrefixCut := [⟨64,291977235,291977403⟩]
theorem checked43202 : checkPrefixCuts (2^48) 5666504705 10 Manual.Count131072.C043202.packed 64 cuts43202 = true := by
 decide +kernel
def cuts43203 : List PrefixCut := [⟨19,84045263,84045315⟩,
⟨64,289039812,289039982⟩]
theorem checked43203 : checkPrefixCuts (2^48) 5666635777 10 Manual.Count131072.C043203.packed 64 cuts43203 = true := by
 decide +kernel
def pointBounds43203 : List (Nat × Nat × Nat) := [(5666674688,109832754980741,109833141054593)]
theorem point_links_checked43203 : (cuts43203.take 1).map (fun c => (5666635777-1+2*2^10*c.k,109832670935478+c.lower,109833057009278+c.upper)) = pointBounds43203 := by
 decide +kernel
def cuts43204 : List PrefixCut := [⟨42,194014085,194014201⟩,
⟨64,294049879,294050053⟩]
theorem checked43204 : checkPrefixCuts (2^48) 5666766849 10 Manual.Count131072.C043204.packed 64 cuts43204 = true := by
 decide +kernel
def pointBounds43204 : List (Nat × Nat × Nat) := [(5666852864,109833153989375,109833540063461)]
theorem point_links_checked43204 : (cuts43204.take 1).map (fun c => (5666766849-1+2*2^10*c.k,109832959975290+c.lower,109833346049260+c.upper)) = pointBounds43204 := by
 decide +kernel
def cuts43205 : List PrefixCut := [⟨64,292056288,292056458⟩]
theorem checked43205 : checkPrefixCuts (2^48) 5666897921 10 Manual.Count131072.C043205.packed 64 cuts43205 = true := by
 decide +kernel
def cuts43206 : List PrefixCut := [⟨1,4569535,4569537⟩,
⟨64,286685343,286685506⟩]
theorem checked43206 : checkPrefixCuts (2^48) 5667028993 10 Manual.Count131072.C043206.packed 64 cuts43206 = true := by
 decide +kernel
def pointBounds43206 : List (Nat × Nat × Nat) := [(5667031040,109833550650992,109833936725308)]
theorem point_links_checked43206 : (cuts43206.take 1).map (fun c => (5667028993-1+2*2^10*c.k,109833546081457+c.lower,109833932155771+c.upper)) = pointBounds43206 := by
 decide +kernel
def cuts43207 : List PrefixCut := [⟨24,106089783,106089844⟩,
⟨64,285387392,285387556⟩]
theorem checked43207 : checkPrefixCuts (2^48) 5667160065 10 Manual.Count131072.C043207.packed 64 cuts43207 = true := by
 decide +kernel
def pointBounds43207 : List (Nat × Nat × Nat) := [(5667209216,109833938856583,109834324931121)]
theorem point_links_checked43207 : (cuts43207.take 1).map (fun c => (5667160065-1+2*2^10*c.k,109833832766800+c.lower,109834218841277+c.upper)) = pointBounds43207 := by
 decide +kernel
def cuts43208 : List PrefixCut := [⟨47,214557754,214557881⟩,
⟨64,294519324,294519494⟩]
theorem checked43208 : checkPrefixCuts (2^48) 5667291137 10 Manual.Count131072.C043208.packed 64 cuts43208 = true := by
 decide +kernel
def pointBounds43208 : List (Nat × Nat × Nat) := [(5667387392,109834332711946,109834718786714)]
theorem point_links_checked43208 : (cuts43208.take 1).map (fun c => (5667291137-1+2*2^10*c.k,109834118154192+c.lower,109834504228833+c.upper)) = pointBounds43208 := by
 decide +kernel
def cuts43209 : List PrefixCut := [⟨64,288900408,288900576⟩]
theorem checked43209 : checkPrefixCuts (2^48) 5667422209 10 Manual.Count131072.C043209.packed 64 cuts43209 = true := by
 decide +kernel
def cuts43210 : List PrefixCut := [⟨6,26769013,26769029⟩,
⟨64,289440016,289440187⟩]
theorem checked43210 : checkPrefixCuts (2^48) 5667553281 10 Manual.Count131072.C043210.packed 64 cuts43210 = true := by
 decide +kernel
def pointBounds43210 : List (Nat × Nat × Nat) := [(5667565568,109834728342937,109835114417932)]
theorem point_links_checked43210 : (cuts43210.take 1).map (fun c => (5667553281-1+2*2^10*c.k,109834701573924+c.lower,109835087648903+c.upper)) = pointBounds43210 := by
 decide +kernel
def cuts43211 : List PrefixCut := [⟨29,130662990,130663061⟩,
⟨64,291320496,291320659⟩]
theorem checked43211 : checkPrefixCuts (2^48) 5667684353 10 Manual.Count131072.C043211.packed 64 cuts43211 = true := by
 decide +kernel
def pointBounds43211 : List (Nat × Nat × Nat) := [(5667743744,109835121676930,109835507752151)]
theorem point_links_checked43211 : (cuts43211.take 1).map (fun c => (5667684353-1+2*2^10*c.k,109834991013940+c.lower,109835377089090+c.upper)) = pointBounds43211 := by
 decide +kernel
def cuts43212 : List PrefixCut := [⟨52,236637075,236637209⟩,
⟨64,292009016,292009181⟩]
theorem checked43212 : checkPrefixCuts (2^48) 5667815425 10 Manual.Count131072.C043212.packed 64 cuts43212 = true := by
 decide +kernel
def pointBounds43212 : List (Nat × Nat × Nat) := [(5667921920,109835518971511,109835905046958)]
theorem point_links_checked43212 : (cuts43212.take 1).map (fun c => (5667815425-1+2*2^10*c.k,109835282334436+c.lower,109835668409749+c.upper)) = pointBounds43212 := by
 decide +kernel
def cuts43213 : List PrefixCut := [⟨64,288923321,288923487⟩]
theorem checked43213 : checkPrefixCuts (2^48) 5667946497 10 Manual.Count131072.C043213.packed 64 cuts43213 = true := by
 decide +kernel
def cuts43214 : List PrefixCut := [⟨11,51050048,51050077⟩,
⟨64,292591437,292591609⟩]
theorem checked43214 : checkPrefixCuts (2^48) 5668077569 10 Manual.Count131072.C043214.packed 64 cuts43214 = true := by
 decide +kernel
def pointBounds43214 : List (Nat × Nat × Nat) := [(5668100096,109835914316821,109836300392494)]
theorem point_links_checked43214 : (cuts43214.take 1).map (fun c => (5668077569-1+2*2^10*c.k,109835863266773+c.lower,109836249342417+c.upper)) = pointBounds43214 := by
 decide +kernel
def cuts43215 : List PrefixCut := [⟨34,156274421,156274511⟩,
⟨64,292435695,292435865⟩]
theorem checked43215 : checkPrefixCuts (2^48) 5668208641 10 Manual.Count131072.C043215.packed 64 cuts43215 = true := by
 decide +kernel
def pointBounds43215 : List (Nat × Nat × Nat) := [(5668278272,109836312132631,109836698208537)]
theorem point_links_checked43215 : (cuts43215.take 1).map (fun c => (5668208641-1+2*2^10*c.k,109836155858210+c.lower,109836541934026+c.upper)) = pointBounds43215 := by
 decide +kernel
def cuts43216 : List PrefixCut := [⟨57,261840660,261840819⟩,
⟨64,293521376,293521553⟩]
theorem checked43216 : checkPrefixCuts (2^48) 5668339713 10 Manual.Count131072.C043216.packed 64 cuts43216 = true := by
 decide +kernel
def pointBounds43216 : List (Nat × Nat × Nat) := [(5668456448,109836710134565,109837096210710)]
theorem point_links_checked43216 : (cuts43216.take 1).map (fun c => (5668339713-1+2*2^10*c.k,109836448293905+c.lower,109836834369891+c.upper)) = pointBounds43216 := by
 decide +kernel
def cuts43217 : List PrefixCut := [⟨64,286463482,286463648⟩]
theorem checked43217 : checkPrefixCuts (2^48) 5668470785 10 Manual.Count131072.C043217.packed 64 cuts43217 = true := by
 decide +kernel
def cuts43218 : List PrefixCut := [⟨16,73092068,73092112⟩,
⟨64,294798815,294798985⟩]
theorem checked43218 : checkPrefixCuts (2^48) 5668601857 10 Manual.Count131072.C043218.packed 64 cuts43218 = true := by
 decide +kernel
def pointBounds43218 : List (Nat × Nat × Nat) := [(5668634624,109837101370831,109837487447204)]
theorem point_links_checked43218 : (cuts43218.take 1).map (fun c => (5668601857-1+2*2^10*c.k,109837028278763+c.lower,109837414355092+c.upper)) = pointBounds43218 := by
 decide +kernel
def cuts43219 : List PrefixCut := [⟨39,179944587,179944688⟩,
⟨64,293103800,293103967⟩]
theorem checked43219 : checkPrefixCuts (2^48) 5668732929 10 Manual.Count131072.C043219.packed 64 cuts43219 = true := by
 decide +kernel
def pointBounds43219 : List (Nat × Nat × Nat) := [(5668812800,109837503022165,109837889098765)]
theorem point_links_checked43219 : (cuts43219.take 1).map (fun c => (5668732929-1+2*2^10*c.k,109837323077578+c.lower,109837709154077+c.upper)) = pointBounds43219 := by
 decide +kernel
def cuts43220 : List PrefixCut := [⟨62,282123963,282124122⟩,
⟨64,291458475,291458639⟩]
theorem checked43220 : checkPrefixCuts (2^48) 5668864001 10 Manual.Count131072.C043220.packed 64 cuts43220 = true := by
 decide +kernel
def pointBounds43220 : List (Nat × Nat × Nat) := [(5668990976,109837898305341,109838284382166)]
theorem point_links_checked43220 : (cuts43220.take 1).map (fun c => (5668864001-1+2*2^10*c.k,109837616181378+c.lower,109838002258044+c.upper)) = pointBounds43220 := by
 decide +kernel
def cuts43221 : List PrefixCut := [⟨64,288770583,288770753⟩]
theorem checked43221 : checkPrefixCuts (2^48) 5668995073 10 Manual.Count131072.C043221.packed 64 cuts43221 = true := by
 decide +kernel
def cuts43222 : List PrefixCut := [⟨21,95775430,95775484⟩,
⟨64,289905850,289906015⟩]
theorem checked43222 : checkPrefixCuts (2^48) 5669126145 10 Manual.Count131072.C043222.packed 64 cuts43222 = true := by
 decide +kernel
def pointBounds43222 : List (Nat × Nat × Nat) := [(5669169152,109838292185866,109838678262920)]
theorem point_links_checked43222 : (cuts43222.take 1).map (fun c => (5669126145-1+2*2^10*c.k,109838196410436+c.lower,109838582487436+c.upper)) = pointBounds43222 := by
 decide +kernel
def cuts43223 : List PrefixCut := [⟨44,200234194,200234313⟩,
⟨64,292580165,292580337⟩]
theorem checked43223 : checkPrefixCuts (2^48) 5669257217 10 Manual.Count131072.C043223.packed 64 cuts43223 = true := by
 decide +kernel
def pointBounds43223 : List (Nat × Nat × Nat) := [(5669347328,109838686550480,109839072627764)]
theorem point_links_checked43223 : (cuts43223.take 1).map (fun c => (5669257217-1+2*2^10*c.k,109838486316286+c.lower,109838872393451+c.upper)) = pointBounds43223 := by
 decide +kernel
def cuts43224 : List PrefixCut := [⟨64,288204434,288204609⟩]
theorem checked43224 : checkPrefixCuts (2^48) 5669388289 10 Manual.Count131072.C043224.packed 64 cuts43224 = true := by
 decide +kernel
def cuts43225 : List PrefixCut := [⟨3,13901166,13901175⟩,
⟨64,286410532,286410694⟩]
theorem checked43225 : checkPrefixCuts (2^48) 5669519361 10 Manual.Count131072.C043225.packed 64 cuts43225 = true := by
 decide +kernel
def pointBounds43225 : List (Nat × Nat × Nat) := [(5669525504,109839081002051,109839467079572)]
theorem point_links_checked43225 : (cuts43225.take 1).map (fun c => (5669519361-1+2*2^10*c.k,109839067100885+c.lower,109839453178397+c.upper)) = pointBounds43225 := by
 decide +kernel
def cuts43226 : List PrefixCut := [⟨26,117809160,117809229⟩,
⟨64,289432234,289432407⟩]
theorem checked43226 : checkPrefixCuts (2^48) 5669650433 10 Manual.Count131072.C043226.packed 64 cuts43226 = true := by
 decide +kernel
def pointBounds43226 : List (Nat × Nat × Nat) := [(5669703680,109839471320577,109839857398320)]
theorem point_links_checked43226 : (cuts43226.take 1).map (fun c => (5669650433-1+2*2^10*c.k,109839353511417+c.lower,109839739589091+c.upper)) = pointBounds43226 := by
 decide +kernel
def cuts43227 : List PrefixCut := [⟨49,221215070,221215203⟩,
⟨64,287241241,287241412⟩]
theorem checked43227 : checkPrefixCuts (2^48) 5669781505 10 Manual.Count131072.C043227.packed 64 cuts43227 = true := by
 decide +kernel
def pointBounds43227 : List (Nat × Nat × Nat) := [(5669881856,109839864158721,109840250236701)]
theorem point_links_checked43227 : (cuts43227.take 1).map (fun c => (5669781505-1+2*2^10*c.k,109839642943651+c.lower,109840029021498+c.upper)) = pointBounds43227 := by
 decide +kernel
def cuts43228 : List PrefixCut := [⟨64,289915311,289915482⟩]
theorem checked43228 : checkPrefixCuts (2^48) 5669912577 10 Manual.Count131072.C043228.packed 64 cuts43228 = true := by
 decide +kernel
def cuts43229 : List PrefixCut := [⟨8,35196451,35196473⟩,
⟨64,287724347,287724515⟩]
theorem checked43229 : checkPrefixCuts (2^48) 5670043649 10 Manual.Count131072.C043229.packed 64 cuts43229 = true := by
 decide +kernel
def pointBounds43229 : List (Nat × Nat × Nat) := [(5670060032,109840255296654,109840641374865)]
theorem point_links_checked43229 : (cuts43229.take 1).map (fun c => (5670043649-1+2*2^10*c.k,109840220100203+c.lower,109840606178392+c.upper)) = pointBounds43229 := by
 decide +kernel
def cuts43230 : List PrefixCut := [⟨31,137654576,137654655⟩,
⟨64,285285288,285285454⟩]
theorem checked43230 : checkPrefixCuts (2^48) 5670174721 10 Manual.Count131072.C043230.packed 64 cuts43230 = true := by
 decide +kernel
def pointBounds43230 : List (Nat × Nat × Nat) := [(5670238208,109840645479126,109841031557562)]
theorem point_links_checked43230 : (cuts43230.take 1).map (fun c => (5670174721-1+2*2^10*c.k,109840507824550+c.lower,109840893902907+c.upper)) = pointBounds43230 := by
 decide +kernel
def cuts43231 : List PrefixCut := [⟨54,245617147,245617290⟩,
⟨64,291334763,291334931⟩]
theorem checked43231 : checkPrefixCuts (2^48) 5670305793 10 Manual.Count131072.C043231.packed 64 cuts43231 = true := by
 decide +kernel
def pointBounds43231 : List (Nat × Nat × Nat) := [(5670416384,109841038726985,109841424805651)]
theorem point_links_checked43231 : (cuts43231.take 1).map (fun c => (5670305793-1+2*2^10*c.k,109840793109838+c.lower,109841179188361+c.upper)) = pointBounds43231 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S5.B000100
