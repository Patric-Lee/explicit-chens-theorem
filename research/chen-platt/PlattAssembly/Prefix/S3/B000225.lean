import PlattAssemblyKernel
import PlattCertificates.Count131072.C027200
import PlattCertificates.Count131072.C027201
import PlattCertificates.Count131072.C027202
import PlattCertificates.Count131072.C027203
import PlattCertificates.Count131072.C027204
import PlattCertificates.Count131072.C027205
import PlattCertificates.Count131072.C027206
import PlattCertificates.Count131072.C027207
import PlattCertificates.Count131072.C027208
import PlattCertificates.Count131072.C027209
import PlattCertificates.Count131072.C027210
import PlattCertificates.Count131072.C027211
import PlattCertificates.Count131072.C027212
import PlattCertificates.Count131072.C027213
import PlattCertificates.Count131072.C027214
import PlattCertificates.Count131072.C027215
import PlattCertificates.Count131072.C027216
import PlattCertificates.Count131072.C027217
import PlattCertificates.Count131072.C027218
import PlattCertificates.Count131072.C027219
import PlattCertificates.Count131072.C027220
import PlattCertificates.Count131072.C027221
import PlattCertificates.Count131072.C027222
import PlattCertificates.Count131072.C027223
import PlattCertificates.Count131072.C027224
import PlattCertificates.Count131072.C027225
import PlattCertificates.Count131072.C027226
import PlattCertificates.Count131072.C027227
import PlattCertificates.Count131072.C027228
import PlattCertificates.Count131072.C027229
import PlattCertificates.Count131072.C027230
import PlattCertificates.Count131072.C027231
namespace ChenEffective.PlattWindow.Assembly.Prefix.S3.B000225
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts27200 : List PrefixCut := [⟨58,217270157,217270279⟩,
⟨128,478620473,478620738⟩]
theorem checked27200 : checkPrefixCuts (2^48) 3569090561 9 Manual.Count131072.C027200.packed 128 cuts27200 = true := by
 decide +kernel
def pointBounds27200 : List (Nat × Nat × Nat) := [(3569149952,103978440919103,103978823540539)]
theorem point_links_checked27200 : (cuts27200.take 1).map (fun c => (3569090561-1+2*2^9*c.k,103978223648946+c.lower,103978606270260+c.upper)) = pointBounds27200 := by
 decide +kernel
def cuts27201 : List PrefixCut := [⟨39,142738883,142738962⟩,
⟨128,468587642,468587901⟩]
theorem checked27201 : checkPrefixCuts (2^48) 3569221633 9 Manual.Count131072.C027201.packed 128 cuts27201 = true := by
 decide +kernel
def pointBounds27201 : List (Nat × Nat × Nat) := [(3569261568,103978845008302,103979227629960)]
theorem point_links_checked27201 : (cuts27201.take 1).map (fun c => (3569221633-1+2*2^9*c.k,103978702269419+c.lower,103979084890998+c.upper)) = pointBounds27201 := by
 decide +kernel
def cuts27202 : List PrefixCut := [⟨20,75625377,75625420⟩,
⟨128,479531639,479531909⟩]
theorem checked27202 : checkPrefixCuts (2^48) 3569352705 9 Manual.Count131072.C027202.packed 128 cuts27202 = true := by
 decide +kernel
def pointBounds27202 : List (Nat × Nat × Nat) := [(3569373184,103979246482438,103979629104319)]
theorem point_links_checked27202 : (cuts27202.take 1).map (fun c => (3569352705-1+2*2^9*c.k,103979170857061+c.lower,103979553478899+c.upper)) = pointBounds27202 := by
 decide +kernel
def cuts27203 : List PrefixCut := [⟨1,3785083,3785085⟩,
⟨110,406732420,406732646⟩,
⟨128,471707470,471707733⟩]
theorem checked27203 : checkPrefixCuts (2^48) 3569483777 9 Manual.Count131072.C027203.packed 128 cuts27203 = true := by
 decide +kernel
def pointBounds27203 : List (Nat × Nat × Nat) := [(3569484800,103979654173783,103980036795893),(3569596416,103980057121120,103980439743454)]
theorem point_links_checked27203 : (cuts27203.take 2).map (fun c => (3569483777-1+2*2^9*c.k,103979650388700+c.lower,103980033010808+c.upper)) = pointBounds27203 := by
 decide +kernel
def cuts27204 : List PrefixCut := [⟨91,334017000,334017192⟩,
⟨128,469009129,469009395⟩]
theorem checked27204 : checkPrefixCuts (2^48) 3569614849 9 Manual.Count131072.C027204.packed 128 cuts27204 = true := by
 decide +kernel
def pointBounds27204 : List (Nat × Nat × Nat) := [(3569708032,103980456113170,103980838735733)]
theorem point_links_checked27204 : (cuts27204.take 1).map (fun c => (3569614849-1+2*2^9*c.k,103980122096170+c.lower,103980504718541+c.upper)) = pointBounds27204 := by
 decide +kernel
def cuts27205 : List PrefixCut := [⟨72,263908610,263908758⟩,
⟨128,474905482,474905746⟩]
theorem checked27205 : checkPrefixCuts (2^48) 3569745921 9 Manual.Count131072.C027205.packed 128 cuts27205 = true := by
 decide +kernel
def pointBounds27205 : List (Nat × Nat × Nat) := [(3569819648,103980855013909,103981237636694)]
theorem point_links_checked27205 : (cuts27205.take 1).map (fun c => (3569745921-1+2*2^9*c.k,103980591105299+c.lower,103980973727936+c.upper)) = pointBounds27205 := by
 decide +kernel
def cuts27206 : List PrefixCut := [⟨53,193331917,193332026⟩,
⟨128,468107352,468107613⟩]
theorem checked27206 : checkPrefixCuts (2^48) 3569876993 9 Manual.Count131072.C027206.packed 128 cuts27206 = true := by
 decide +kernel
def pointBounds27206 : List (Nat × Nat × Nat) := [(3569931264,103981259342698,103981641965708)]
theorem point_links_checked27206 : (cuts27206.take 1).map (fun c => (3569876993-1+2*2^9*c.k,103981066010781+c.lower,103981448633682+c.upper)) = pointBounds27206 := by
 decide +kernel
def cuts27207 : List PrefixCut := [⟨34,125361864,125361934⟩,
⟨128,471638195,471638457⟩]
theorem checked27207 : checkPrefixCuts (2^48) 3570008065 9 Manual.Count131072.C027207.packed 128 cuts27207 = true := by
 decide +kernel
def pointBounds27207 : List (Nat × Nat × Nat) := [(3570042880,103981659479997,103982042103229)]
theorem point_links_checked27207 : (cuts27207.take 1).map (fun c => (3570008065-1+2*2^9*c.k,103981534118133+c.lower,103981916741295+c.upper)) = pointBounds27207 := by
 decide +kernel
def cuts27208 : List PrefixCut := [⟨15,55583092,55583125⟩,
⟨124,454039754,454040009⟩,
⟨128,468388377,468388640⟩]
theorem checked27208 : checkPrefixCuts (2^48) 3570139137 9 Manual.Count131072.C027208.packed 128 cuts27208 = true := by
 decide +kernel
def pointBounds27208 : List (Nat × Nat × Nat) := [(3570154496,103982061339420,103982443962877),(3570266112,103982459796082,103982842419761)]
theorem point_links_checked27208 : (cuts27208.take 2).map (fun c => (3570139137-1+2*2^9*c.k,103982005756328+c.lower,103982388379752+c.upper)) = pointBounds27208 := by
 decide +kernel
def cuts27209 : List PrefixCut := [⟨105,389693012,389693230⟩,
⟨128,473889769,473890034⟩]
theorem checked27209 : checkPrefixCuts (2^48) 3570270209 9 Manual.Count131072.C027209.packed 128 cuts27209 = true := by
 decide +kernel
def pointBounds27209 : List (Nat × Nat × Nat) := [(3570377728,103982863837717,103983246461622)]
theorem point_links_checked27209 : (cuts27209.take 1).map (fun c => (3570270209-1+2*2^9*c.k,103982474144705+c.lower,103982856768392+c.upper)) = pointBounds27209 := by
 decide +kernel
def cuts27210 : List PrefixCut := [⟨86,317309544,317309723⟩,
⟨128,467723354,467723620⟩]
theorem checked27210 : checkPrefixCuts (2^48) 3570401281 9 Manual.Count131072.C027210.packed 128 cuts27210 = true := by
 decide +kernel
def pointBounds27210 : List (Nat × Nat × Nat) := [(3570489344,103983265344018,103983647968149)]
theorem point_links_checked27210 : (cuts27210.take 1).map (fun c => (3570401281-1+2*2^9*c.k,103982948034474+c.lower,103983330658426+c.upper)) = pointBounds27210 := by
 decide +kernel
def cuts27211 : List PrefixCut := [⟨67,248478461,248478596⟩,
⟨128,470071108,470071373⟩]
theorem checked27211 : checkPrefixCuts (2^48) 3570532353 9 Manual.Count131072.C027211.packed 128 cuts27211 = true := by
 decide +kernel
def pointBounds27211 : List (Nat × Nat × Nat) := [(3570600960,103983664236289,103984046860642)]
theorem point_links_checked27211 : (cuts27211.take 1).map (fun c => (3570532353-1+2*2^9*c.k,103983415757828+c.lower,103983798382046+c.upper)) = pointBounds27211 := by
 decide +kernel
def cuts27212 : List PrefixCut := [⟨48,173818653,173818751⟩,
⟨128,465245300,465245561⟩]
theorem checked27212 : checkPrefixCuts (2^48) 3570663425 9 Manual.Count131072.C027212.packed 128 cuts27212 = true := by
 decide +kernel
def pointBounds27212 : List (Nat × Nat × Nat) := [(3570712576,103984059647589,103984442272170)]
theorem point_links_checked27212 : (cuts27212.take 1).map (fun c => (3570663425-1+2*2^9*c.k,103983885828936+c.lower,103984268453419+c.upper)) = pointBounds27212 := by
 decide +kernel
def cuts27213 : List PrefixCut := [⟨29,107756024,107756084⟩,
⟨128,467120046,467120313⟩]
theorem checked27213 : checkPrefixCuts (2^48) 3570794497 9 Manual.Count131072.C027213.packed 128 cuts27213 = true := by
 decide +kernel
def pointBounds27213 : List (Nat × Nat × Nat) := [(3570824192,103984458830260,103984841455064)]
theorem point_links_checked27213 : (cuts27213.take 1).map (fun c => (3570794497-1+2*2^9*c.k,103984351074236+c.lower,103984733698980+c.upper)) = pointBounds27213 := by
 decide +kernel
def cuts27214 : List PrefixCut := [⟨10,36731966,36731988⟩,
⟨119,431317956,431318199⟩,
⟨128,462610005,462610265⟩]
theorem checked27214 : checkPrefixCuts (2^48) 3570925569 9 Manual.Count131072.C027214.packed 128 cuts27214 = true := by
 decide +kernel
def pointBounds27214 : List (Nat × Nat × Nat) := [(3570935808,103984854926248,103985237551281),(3571047424,103985249512238,103985632137492)]
theorem point_links_checked27214 : (cuts27214.take 2).map (fun c => (3570925569-1+2*2^9*c.k,103984818194282+c.lower,103985200819293+c.upper)) = pointBounds27214 := by
 decide +kernel
def cuts27215 : List PrefixCut := [⟨100,366986134,366986343⟩,
⟨128,469292678,469292944⟩]
theorem checked27215 : checkPrefixCuts (2^48) 3571056641 9 Manual.Count131072.C027215.packed 128 cuts27215 = true := by
 decide +kernel
def pointBounds27215 : List (Nat × Nat × Nat) := [(3571159040,103985647790421,103986030415901)]
theorem point_links_checked27215 : (cuts27215.take 1).map (fun c => (3571056641-1+2*2^9*c.k,103985280804287+c.lower,103985663429558+c.upper)) = pointBounds27215 := by
 decide +kernel
def cuts27216 : List PrefixCut := [⟨81,301476448,301476615⟩,
⟨128,473452793,473453058⟩]
theorem checked27216 : checkPrefixCuts (2^48) 3571187713 9 Manual.Count131072.C027216.packed 128 cuts27216 = true := by
 decide +kernel
def pointBounds27216 : List (Nat × Nat × Nat) := [(3571270656,103986051573413,103986434199117)]
theorem point_links_checked27216 : (cuts27216.take 1).map (fun c => (3571187713-1+2*2^9*c.k,103985750096965+c.lower,103986132722502+c.upper)) = pointBounds27216 := by
 decide +kernel
def cuts27217 : List PrefixCut := [⟨62,229744831,229744957⟩,
⟨128,474459949,474460208⟩]
theorem checked27217 : checkPrefixCuts (2^48) 3571318785 9 Manual.Count131072.C027217.packed 128 cuts27217 = true := by
 decide +kernel
def pointBounds27217 : List (Nat × Nat × Nat) := [(3571382272,103986453294589,103986835920517)]
theorem point_links_checked27217 : (cuts27217.take 1).map (fun c => (3571318785-1+2*2^9*c.k,103986223549758+c.lower,103986606175560+c.upper)) = pointBounds27217 := by
 decide +kernel
def cuts27218 : List PrefixCut := [⟨43,158806208,158806292⟩,
⟨128,473339164,473339425⟩]
theorem checked27218 : checkPrefixCuts (2^48) 3571449857 9 Manual.Count131072.C027218.packed 128 cuts27218 = true := by
 decide +kernel
def pointBounds27218 : List (Nat × Nat × Nat) := [(3571493888,103986856815915,103987239442060)]
theorem point_links_checked27218 : (cuts27218.take 1).map (fun c => (3571449857-1+2*2^9*c.k,103986698009707+c.lower,103987080635768+c.upper)) = pointBounds27218 := by
 decide +kernel
def cuts27219 : List PrefixCut := [⟨24,85980986,85981034⟩,
⟨128,471903254,471903515⟩]
theorem checked27219 : checkPrefixCuts (2^48) 3571580929 9 Manual.Count131072.C027219.packed 128 cuts27219 = true := by
 decide +kernel
def pointBounds27219 : List (Nat × Nat × Nat) := [(3571605504,103987257329857,103987639956227)]
theorem point_links_checked27219 : (cuts27219.take 1).map (fun c => (3571580929-1+2*2^9*c.k,103987171348871+c.lower,103987553975193+c.upper)) = pointBounds27219 := by
 decide +kernel
def cuts27220 : List PrefixCut := [⟨5,17967918,17967929⟩,
⟨114,418535609,418535844⟩,
⟨128,469206569,469206833⟩]
theorem checked27220 : checkPrefixCuts (2^48) 3571712001 9 Manual.Count131072.C027220.packed 128 cuts27220 = true := by
 decide +kernel
def pointBounds27220 : List (Nat × Nat × Nat) := [(3571717120,103987661220043,103988043846637),(3571828736,103988061787734,103988444414552)]
theorem point_links_checked27220 : (cuts27220.take 2).map (fun c => (3571712001-1+2*2^9*c.k,103987643252125+c.lower,103988025878708+c.upper)) = pointBounds27220 := by
 decide +kernel
def cuts27221 : List PrefixCut := [⟨96,351223855,351224053⟩,
⟨128,470371422,470371686⟩]
theorem checked27221 : checkPrefixCuts (2^48) 3571843073 9 Manual.Count131072.C027221.packed 128 cuts27221 = true := by
 decide +kernel
def pointBounds27221 : List (Nat × Nat × Nat) := [(3571941376,103988463682549,103988846309594)]
theorem point_links_checked27221 : (cuts27221.take 1).map (fun c => (3571843073-1+2*2^9*c.k,103988112458694+c.lower,103988495085541+c.upper)) = pointBounds27221 := by
 decide +kernel
def cuts27222 : List PrefixCut := [⟨78,286280583,286280745⟩,
⟨128,466808197,466808462⟩]
theorem checked27222 : checkPrefixCuts (2^48) 3571974145 9 Manual.Count131072.C027222.packed 128 cuts27222 = true := by
 decide +kernel
def pointBounds27222 : List (Nat × Nat × Nat) := [(3572054016,103988869110699,103989251737972)]
theorem point_links_checked27222 : (cuts27222.take 1).map (fun c => (3571974145-1+2*2^9*c.k,103988582830116+c.lower,103988965457227+c.upper)) = pointBounds27222 := by
 decide +kernel
def cuts27223 : List PrefixCut := [⟨60,217717114,217717240⟩,
⟨128,470336834,470337099⟩]
theorem checked27223 : checkPrefixCuts (2^48) 3572105217 9 Manual.Count131072.C027223.packed 128 cuts27223 = true := by
 decide +kernel
def pointBounds27223 : List (Nat × Nat × Nat) := [(3572166656,103989267355427,103989649982929)]
theorem point_links_checked27223 : (cuts27223.take 1).map (fun c => (3572105217-1+2*2^9*c.k,103989049638313+c.lower,103989432265689+c.upper)) = pointBounds27223 := by
 decide +kernel
def cuts27224 : List PrefixCut := [⟨42,150576628,150576709⟩,
⟨128,464410034,464410293⟩]
theorem checked27224 : checkPrefixCuts (2^48) 3572236289 9 Manual.Count131072.C027224.packed 128 cuts27224 = true := by
 decide +kernel
def pointBounds27224 : List (Nat × Nat × Nat) := [(3572279296,103989670551775,103990053179497)]
theorem point_links_checked27224 : (cuts27224.take 1).map (fun c => (3572236289-1+2*2^9*c.k,103989519975147+c.lower,103989902602788+c.upper)) = pointBounds27224 := by
 decide +kernel
def cuts27225 : List PrefixCut := [⟨24,84543806,84543853⟩,
⟨128,463999145,463999400⟩]
theorem checked27225 : checkPrefixCuts (2^48) 3572367361 9 Manual.Count131072.C027225.packed 128 cuts27225 = true := by
 decide +kernel
def pointBounds27225 : List (Nat × Nat × Nat) := [(3572391936,103990068928987,103990451556934)]
theorem point_links_checked27225 : (cuts27225.take 1).map (fun c => (3572367361-1+2*2^9*c.k,103989984385181+c.lower,103990367013081+c.upper)) = pointBounds27225 := by
 decide +kernel
def cuts27226 : List PrefixCut := [⟨6,22454952,22454964⟩,
⟨116,429079735,429079976⟩,
⟨128,472018437,472018702⟩]
theorem checked27226 : checkPrefixCuts (2^48) 3572498433 9 Manual.Count131072.C027226.packed 128 cuts27226 = true := by
 decide +kernel
def pointBounds27226 : List (Nat × Nat × Nat) := [(3572504576,103990470839278,103990853467445),(3572617216,103990877464061,103991260092457)]
theorem point_links_checked27226 : (cuts27226.take 2).map (fun c => (3572498433-1+2*2^9*c.k,103990448384326+c.lower,103990831012481+c.upper)) = pointBounds27226 := by
 decide +kernel
def cuts27227 : List PrefixCut := [⟨98,361230886,361231090⟩,
⟨128,472788922,472789187⟩]
theorem checked27227 : checkPrefixCuts (2^48) 3572629505 9 Manual.Count131072.C027227.packed 128 cuts27227 = true := by
 decide +kernel
def pointBounds27227 : List (Nat × Nat × Nat) := [(3572729856,103991281633649,103991664262273)]
theorem point_links_checked27227 : (cuts27227.take 1).map (fun c => (3572629505-1+2*2^9*c.k,103990920402763+c.lower,103991303031183+c.upper)) = pointBounds27227 := by
 decide +kernel
def cuts27228 : List PrefixCut := [⟨80,289841489,289841653⟩,
⟨128,465838784,465839043⟩]
theorem checked27228 : checkPrefixCuts (2^48) 3572760577 9 Manual.Count131072.C027228.packed 128 cuts27228 = true := by
 decide +kernel
def pointBounds27228 : List (Nat × Nat × Nat) := [(3572842496,103991683033174,103992065662023)]
theorem point_links_checked27228 : (cuts27228.take 1).map (fun c => (3572760577-1+2*2^9*c.k,103991393191685+c.lower,103991775820370+c.upper)) = pointBounds27228 := by
 decide +kernel
def cuts27229 : List PrefixCut := [⟨62,222002035,222002156⟩,
⟨128,463773415,463773672⟩]
theorem checked27229 : checkPrefixCuts (2^48) 3572891649 9 Manual.Count131072.C027229.packed 128 cuts27229 = true := by
 decide +kernel
def pointBounds27229 : List (Nat × Nat × Nat) := [(3572955136,103992081032504,103992463661569)]
theorem point_links_checked27229 : (cuts27229.take 1).map (fun c => (3572891649-1+2*2^9*c.k,103991859030469+c.lower,103992241659413+c.upper)) = pointBounds27229 := by
 decide +kernel
def cuts27230 : List PrefixCut := [⟨44,162675150,162675240⟩,
⟨128,472973315,472973578⟩]
theorem checked27230 : checkPrefixCuts (2^48) 3573022721 9 Manual.Count131072.C027230.packed 128 cuts27230 = true := by
 decide +kernel
def pointBounds27230 : List (Nat × Nat × Nat) := [(3573067776,103992485479034,103992868108325)]
theorem point_links_checked27230 : (cuts27230.take 1).map (fun c => (3573022721-1+2*2^9*c.k,103992322803884+c.lower,103992705433085+c.upper)) = pointBounds27230 := by
 decide +kernel
def cuts27231 : List PrefixCut := [⟨26,94844654,94844708⟩,
⟨128,471538010,471538274⟩]
theorem checked27231 : checkPrefixCuts (2^48) 3573153793 9 Manual.Count131072.C027231.packed 128 cuts27231 = true := by
 decide +kernel
def pointBounds27231 : List (Nat × Nat × Nat) := [(3573180416,103992890621853,103993273251371)]
theorem point_links_checked27231 : (cuts27231.take 1).map (fun c => (3573153793-1+2*2^9*c.k,103992795777199+c.lower,103993178406663+c.upper)) = pointBounds27231 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S3.B000225
