import PlattAssemblyKernel
import PlattCertificates.Count131072.C032048
import PlattCertificates.Count131072.C032049
import PlattCertificates.Count131072.C032050
import PlattCertificates.Count131072.C032051
import PlattCertificates.Count131072.C032052
import PlattCertificates.Count131072.C032053
import PlattCertificates.Count131072.C032054
import PlattCertificates.Count131072.C032055
import PlattCertificates.Count131072.C032056
import PlattCertificates.Count131072.C032057
import PlattCertificates.Count131072.C032058
import PlattCertificates.Count131072.C032059
import PlattCertificates.Count131072.C032060
import PlattCertificates.Count131072.C032061
import PlattCertificates.Count131072.C032062
import PlattCertificates.Count131072.C032063
import PlattCertificates.Count131072.C032064
import PlattCertificates.Count131072.C032065
import PlattCertificates.Count131072.C032066
import PlattCertificates.Count131072.C032067
import PlattCertificates.Count131072.C032068
import PlattCertificates.Count131072.C032069
import PlattCertificates.Count131072.C032070
import PlattCertificates.Count131072.C032071
import PlattCertificates.Count131072.C032072
import PlattCertificates.Count131072.C032073
import PlattCertificates.Count131072.C032074
import PlattCertificates.Count131072.C032075
import PlattCertificates.Count131072.C032076
import PlattCertificates.Count131072.C032077
import PlattCertificates.Count131072.C032078
import PlattCertificates.Count131072.C032079
namespace ChenEffective.PlattWindow.Assembly.Prefix.S4.B000064
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts32048 : List PrefixCut := [⟨52,155446844,155446932⟩,
⟨128,392027653,392027874⟩]
theorem checked32048 : checkPrefixCuts (2^48) 4204527617 9 Manual.Count131072.C032048.packed 128 cuts32048 = true := by
 decide +kernel
def pointBounds32048 : List (Nat × Nat × Nat) := [(4204580864,106067332908404,106067716702883)]
theorem point_links_checked32048 : (cuts32048.take 1).map (fun c => (4204527617-1+2*2^9*c.k,106067177461560+c.lower,106067561255951+c.upper)) = pointBounds32048 := by
 decide +kernel
def cuts32049 : List PrefixCut := [⟨53,168763675,168763769⟩,
⟨128,404466831,404467049⟩]
theorem checked32049 : checkPrefixCuts (2^48) 4204658689 9 Manual.Count131072.C032049.packed 128 cuts32049 = true := by
 decide +kernel
def pointBounds32049 : List (Nat × Nat × Nat) := [(4204712960,106067738252888,106068122047594)]
theorem point_links_checked32049 : (cuts32049.take 1).map (fun c => (4204658689-1+2*2^9*c.k,106067569489213+c.lower,106067953283825+c.upper)) = pointBounds32049 := by
 decide +kernel
def cuts32050 : List PrefixCut := [⟨54,168959211,168959310⟩,
⟨128,394948678,394948909⟩]
theorem checked32050 : checkPrefixCuts (2^48) 4204789761 9 Manual.Count131072.C032050.packed 128 cuts32050 = true := by
 decide +kernel
def pointBounds32050 : List (Nat × Nat × Nat) := [(4204845056,106068142915255,106068526710184)]
theorem point_links_checked32050 : (cuts32050.take 1).map (fun c => (4204789761-1+2*2^9*c.k,106067973956044+c.lower,106068357750874+c.upper)) = pointBounds32050 := by
 decide +kernel
def cuts32051 : List PrefixCut := [⟨55,172167010,172167108⟩,
⟨128,397480021,397480246⟩]
theorem checked32051 : checkPrefixCuts (2^48) 4204920833 9 Manual.Count131072.C032051.packed 128 cuts32051 = true := by
 decide +kernel
def pointBounds32051 : List (Nat × Nat × Nat) := [(4204977152,106068541071732,106068924866891)]
theorem point_links_checked32051 : (cuts32051.take 1).map (fun c => (4204920833-1+2*2^9*c.k,106068368904722+c.lower,106068752699783+c.upper)) = pointBounds32051 := by
 decide +kernel
def cuts32052 : List PrefixCut := [⟨56,173500334,173500431⟩,
⟨128,396865187,396865408⟩]
theorem checked32052 : checkPrefixCuts (2^48) 4205051905 9 Manual.Count131072.C032052.packed 128 cuts32052 = true := by
 decide +kernel
def pointBounds32052 : List (Nat × Nat × Nat) := [(4205109248,106068939885077,106069323680460)]
theorem point_links_checked32052 : (cuts32052.take 1).map (fun c => (4205051905-1+2*2^9*c.k,106068766384743+c.lower,106069150180029+c.upper)) = pointBounds32052 := by
 decide +kernel
def cuts32053 : List PrefixCut := [⟨57,175837635,175837734⟩,
⟨128,393840787,393841010⟩]
theorem checked32053 : checkPrefixCuts (2^48) 4205182977 9 Manual.Count131072.C032053.packed 128 cuts32053 = true := by
 decide +kernel
def pointBounds32053 : List (Nat × Nat × Nat) := [(4205241344,106069339087565,106069722883171)]
theorem point_links_checked32053 : (cuts32053.take 1).map (fun c => (4205182977-1+2*2^9*c.k,106069163249930+c.lower,106069547045437+c.upper)) = pointBounds32053 := by
 decide +kernel
def cuts32054 : List PrefixCut := [⟨58,176769186,176769290⟩,
⟨128,396840392,396840621⟩]
theorem checked32054 : checkPrefixCuts (2^48) 4205314049 9 Manual.Count131072.C032054.packed 128 cuts32054 = true := by
 decide +kernel
def pointBounds32054 : List (Nat × Nat × Nat) := [(4205373440,106069733859903,106070117655737)]
theorem point_links_checked32054 : (cuts32054.take 1).map (fun c => (4205314049-1+2*2^9*c.k,106069557090717+c.lower,106069940886447+c.upper)) = pointBounds32054 := by
 decide +kernel
def cuts32055 : List PrefixCut := [⟨59,186803236,186803336⟩,
⟨128,399170621,399170846⟩]
theorem checked32055 : checkPrefixCuts (2^48) 4205445121 9 Manual.Count131072.C032055.packed 128 cuts32055 = true := by
 decide +kernel
def pointBounds32055 : List (Nat × Nat × Nat) := [(4205505536,106070140734345,106070524530404)]
theorem point_links_checked32055 : (cuts32055.take 1).map (fun c => (4205445121-1+2*2^9*c.k,106069953931109+c.lower,106070337727068+c.upper)) = pointBounds32055 := by
 decide +kernel
def cuts32056 : List PrefixCut := [⟨60,182982469,182982576⟩,
⟨128,390189820,390190040⟩]
theorem checked32056 : checkPrefixCuts (2^48) 4205576193 9 Manual.Count131072.C032056.packed 128 cuts32056 = true := by
 decide +kernel
def pointBounds32056 : List (Nat × Nat × Nat) := [(4205637632,106070536084199,106070919880490)]
theorem point_links_checked32056 : (cuts32056.take 1).map (fun c => (4205576193-1+2*2^9*c.k,106070353101730+c.lower,106070736897914+c.upper)) = pointBounds32056 := by
 decide +kernel
def cuts32057 : List PrefixCut := [⟨61,188665496,188665609⟩,
⟨128,388705340,388705570⟩]
theorem checked32057 : checkPrefixCuts (2^48) 4205707265 9 Manual.Count131072.C032057.packed 128 cuts32057 = true := by
 decide +kernel
def pointBounds32057 : List (Nat × Nat × Nat) := [(4205769728,106070931957046,106071315753563)]
theorem point_links_checked32057 : (cuts32057.take 1).map (fun c => (4205707265-1+2*2^9*c.k,106070743291550+c.lower,106071127087954+c.upper)) = pointBounds32057 := by
 decide +kernel
def cuts32058 : List PrefixCut := [⟨62,195954348,195954456⟩,
⟨128,395586402,395586627⟩]
theorem checked32058 : checkPrefixCuts (2^48) 4205838337 9 Manual.Count131072.C032058.packed 128 cuts32058 = true := by
 decide +kernel
def pointBounds32058 : List (Nat × Nat × Nat) := [(4205901824,106071327951238,106071711747980)]
theorem point_links_checked32058 : (cuts32058.take 1).map (fun c => (4205838337-1+2*2^9*c.k,106071131996890+c.lower,106071515793524+c.upper)) = pointBounds32058 := by
 decide +kernel
def cuts32059 : List PrefixCut := [⟨63,195278983,195279093⟩,
⟨128,400927710,400927939⟩]
theorem checked32059 : checkPrefixCuts (2^48) 4205969409 9 Manual.Count131072.C032059.packed 128 cuts32059 = true := by
 decide +kernel
def pointBounds32059 : List (Nat × Nat × Nat) := [(4206033920,106071722862275,106072106659244)]
theorem point_links_checked32059 : (cuts32059.take 1).map (fun c => (4205969409-1+2*2^9*c.k,106071527583292+c.lower,106071911380151+c.upper)) = pointBounds32059 := by
 decide +kernel
def cuts32060 : List PrefixCut := [⟨64,192395320,192395433⟩,
⟨128,389739664,389739885⟩]
theorem checked32060 : checkPrefixCuts (2^48) 4206100481 9 Manual.Count131072.C032060.packed 128 cuts32060 = true := by
 decide +kernel
def pointBounds32060 : List (Nat × Nat × Nat) := [(4206166016,106072120906322,106072504703523)]
theorem point_links_checked32060 : (cuts32060.take 1).map (fun c => (4206100481-1+2*2^9*c.k,106071928511002+c.lower,106072312308090+c.upper)) = pointBounds32060 := by
 decide +kernel
def cuts32061 : List PrefixCut := [⟨65,200754059,200754171⟩,
⟨128,397958371,397958593⟩]
theorem checked32061 : checkPrefixCuts (2^48) 4206231553 9 Manual.Count131072.C032061.packed 128 cuts32061 = true := by
 decide +kernel
def pointBounds32061 : List (Nat × Nat × Nat) := [(4206298112,106072519004725,106072902802146)]
theorem point_links_checked32061 : (cuts32061.take 1).map (fun c => (4206231553-1+2*2^9*c.k,106072318250666+c.lower,106072702047975+c.upper)) = pointBounds32061 := by
 decide +kernel
def cuts32062 : List PrefixCut := [⟨66,205164221,205164335⟩,
⟨128,394934827,394935048⟩]
theorem checked32062 : checkPrefixCuts (2^48) 4206362625 9 Manual.Count131072.C032062.packed 128 cuts32062 = true := by
 decide +kernel
def pointBounds32062 : List (Nat × Nat × Nat) := [(4206430208,106072921373258,106073305170903)]
theorem point_links_checked32062 : (cuts32062.take 1).map (fun c => (4206362625-1+2*2^9*c.k,106072716209037+c.lower,106073100006568+c.upper)) = pointBounds32062 := by
 decide +kernel
def cuts32063 : List PrefixCut := [⟨67,204957062,204957178⟩,
⟨128,393718036,393718257⟩]
theorem checked32063 : checkPrefixCuts (2^48) 4206493697 9 Manual.Count131072.C032063.packed 128 cuts32063 = true := by
 decide +kernel
def pointBounds32063 : List (Nat × Nat × Nat) := [(4206562304,106073316100926,106073699898794)]
theorem point_links_checked32063 : (cuts32063.take 1).map (fun c => (4206493697-1+2*2^9*c.k,106073111143864+c.lower,106073494941616+c.upper)) = pointBounds32063 := by
 decide +kernel
def cuts32064 : List PrefixCut := [⟨68,210771974,210772095⟩,
⟨128,398255754,398255980⟩]
theorem checked32064 : checkPrefixCuts (2^48) 4206624769 9 Manual.Count131072.C032064.packed 128 cuts32064 = true := by
 decide +kernel
def pointBounds32064 : List (Nat × Nat × Nat) := [(4206694400,106073715633874,106074099431968)]
theorem point_links_checked32064 : (cuts32064.take 1).map (fun c => (4206624769-1+2*2^9*c.k,106073504861900+c.lower,106073888659873+c.upper)) = pointBounds32064 := by
 decide +kernel
def cuts32065 : List PrefixCut := [⟨69,212571905,212572031⟩,
⟨128,394362567,394362793⟩]
theorem checked32065 : checkPrefixCuts (2^48) 4206755841 9 Manual.Count131072.C032065.packed 128 cuts32065 = true := by
 decide +kernel
def pointBounds32065 : List (Nat × Nat × Nat) := [(4206826496,106074115689559,106074499487884)]
theorem point_links_checked32065 : (cuts32065.take 1).map (fun c => (4206755841-1+2*2^9*c.k,106073903117654+c.lower,106074286915853+c.upper)) = pointBounds32065 := by
 decide +kernel
def cuts32066 : List PrefixCut := [⟨70,217516447,217516570⟩,
⟨128,396692079,396692305⟩]
theorem checked32066 : checkPrefixCuts (2^48) 4206886913 9 Manual.Count131072.C032066.packed 128 cuts32066 = true := by
 decide +kernel
def pointBounds32066 : List (Nat × Nat × Nat) := [(4206958592,106074514996668,106074898795216)]
theorem point_links_checked32066 : (cuts32066.take 1).map (fun c => (4206886913-1+2*2^9*c.k,106074297480221+c.lower,106074681278646+c.upper)) = pointBounds32066 := by
 decide +kernel
def cuts32067 : List PrefixCut := [⟨71,221657795,221657923⟩,
⟨128,397750214,397750444⟩]
theorem checked32067 : checkPrefixCuts (2^48) 4207017985 9 Manual.Count131072.C032067.packed 128 cuts32067 = true := by
 decide +kernel
def pointBounds32067 : List (Nat × Nat × Nat) := [(4207090688,106074915830095,106075299628874)]
theorem point_links_checked32067 : (cuts32067.take 1).map (fun c => (4207017985-1+2*2^9*c.k,106074694172300+c.lower,106075077970951+c.upper)) = pointBounds32067 := by
 decide +kernel
def cuts32068 : List PrefixCut := [⟨72,222520615,222520735⟩,
⟨128,398406823,398407042⟩]
theorem checked32068 : checkPrefixCuts (2^48) 4207149057 9 Manual.Count131072.C032068.packed 128 cuts32068 = true := by
 decide +kernel
def pointBounds32068 : List (Nat × Nat × Nat) := [(4207222784,106075314443129,106075698242130)]
theorem point_links_checked32068 : (cuts32068.take 1).map (fun c => (4207149057-1+2*2^9*c.k,106075091922514+c.lower,106075475721395+c.upper)) = pointBounds32068 := by
 decide +kernel
def cuts32069 : List PrefixCut := [⟨73,223584046,223584176⟩,
⟨128,393309944,393310170⟩]
theorem checked32069 : checkPrefixCuts (2^48) 4207280129 9 Manual.Count131072.C032069.packed 128 cuts32069 = true := by
 decide +kernel
def pointBounds32069 : List (Nat × Nat × Nat) := [(4207354880,106075713913383,106076097712613)]
theorem point_links_checked32069 : (cuts32069.take 1).map (fun c => (4207280129-1+2*2^9*c.k,106075490329337+c.lower,106075874128437+c.upper)) = pointBounds32069 := by
 decide +kernel
def cuts32070 : List PrefixCut := [⟨74,225918516,225918639⟩,
⟨128,392160378,392160588⟩]
theorem checked32070 : checkPrefixCuts (2^48) 4207411201 9 Manual.Count131072.C032070.packed 128 cuts32070 = true := by
 decide +kernel
def pointBounds32070 : List (Nat × Nat × Nat) := [(4207486976,106076109557797,106076493357246)]
theorem point_links_checked32070 : (cuts32070.take 1).map (fun c => (4207411201-1+2*2^9*c.k,106075883639281+c.lower,106076267438607+c.upper)) = pointBounds32070 := by
 decide +kernel
def cuts32071 : List PrefixCut := [⟨75,229791475,229791600⟩,
⟨128,394890912,394891131⟩]
theorem checked32071 : checkPrefixCuts (2^48) 4207542273 9 Manual.Count131072.C032071.packed 128 cuts32071 = true := by
 decide +kernel
def pointBounds32071 : List (Nat × Nat × Nat) := [(4207619072,106076505591134,106076889390795)]
theorem point_links_checked32071 : (cuts32071.take 1).map (fun c => (4207542273-1+2*2^9*c.k,106076275799659+c.lower,106076659599195+c.upper)) = pointBounds32071 := by
 decide +kernel
def cuts32072 : List PrefixCut := [⟨76,234801432,234801559⟩,
⟨128,395547599,395547822⟩]
theorem checked32072 : checkPrefixCuts (2^48) 4207673345 9 Manual.Count131072.C032072.packed 128 cuts32072 = true := by
 decide +kernel
def pointBounds32072 : List (Nat × Nat × Nat) := [(4207751168,106076905492003,106077289291885)]
theorem point_links_checked32072 : (cuts32072.take 1).map (fun c => (4207673345-1+2*2^9*c.k,106076670690571+c.lower,106077054490326+c.upper)) = pointBounds32072 := by
 decide +kernel
def cuts32073 : List PrefixCut := [⟨77,238941444,238941580⟩,
⟨128,399816370,399816597⟩]
theorem checked32073 : checkPrefixCuts (2^48) 4207804417 9 Manual.Count131072.C032073.packed 128 cuts32073 = true := by
 decide +kernel
def pointBounds32073 : List (Nat × Nat × Nat) := [(4207883264,106077305179614,106077688979728)]
theorem point_links_checked32073 : (cuts32073.take 1).map (fun c => (4207804417-1+2*2^9*c.k,106077066238170+c.lower,106077450038148+c.upper)) = pointBounds32073 := by
 decide +kernel
def cuts32074 : List PrefixCut := [⟨78,241408962,241409104⟩,
⟨128,394385849,394386082⟩]
theorem checked32074 : checkPrefixCuts (2^48) 4207935489 9 Manual.Count131072.C032074.packed 128 cuts32074 = true := by
 decide +kernel
def pointBounds32074 : List (Nat × Nat × Nat) := [(4208015360,106077707463502,106078091263849)]
theorem point_links_checked32074 : (cuts32074.take 1).map (fun c => (4207935489-1+2*2^9*c.k,106077466054540+c.lower,106077849854745+c.upper)) = pointBounds32074 := by
 decide +kernel
def cuts32075 : List PrefixCut := [⟨79,245080269,245080415⟩,
⟨128,399189484,399189713⟩]
theorem checked32075 : checkPrefixCuts (2^48) 4208066561 9 Manual.Count131072.C032075.packed 128 cuts32075 = true := by
 decide +kernel
def pointBounds32075 : List (Nat × Nat × Nat) := [(4208147456,106078105520658,106078489321242)]
theorem point_links_checked32075 : (cuts32075.take 1).map (fun c => (4208066561-1+2*2^9*c.k,106077860440389+c.lower,106078244240827+c.upper)) = pointBounds32075 := by
 decide +kernel
def cuts32076 : List PrefixCut := [⟨80,245607684,245607819⟩,
⟨128,393826153,393826373⟩]
theorem checked32076 : checkPrefixCuts (2^48) 4208197633 9 Manual.Count131072.C032076.packed 128 cuts32076 = true := by
 decide +kernel
def pointBounds32076 : List (Nat × Nat × Nat) := [(4208279552,106078505237557,106078889038359)]
theorem point_links_checked32076 : (cuts32076.take 1).map (fun c => (4208197633-1+2*2^9*c.k,106078259629873+c.lower,106078643430540+c.upper)) = pointBounds32076 := by
 decide +kernel
def cuts32077 : List PrefixCut := [⟨81,247272146,247272284⟩,
⟨128,396355461,396355687⟩]
theorem checked32077 : checkPrefixCuts (2^48) 4208328705 9 Manual.Count131072.C032077.packed 128 cuts32077 = true := by
 decide +kernel
def pointBounds32077 : List (Nat × Nat × Nat) := [(4208411648,106078900728172,106079284529197)]
theorem point_links_checked32077 : (cuts32077.take 1).map (fun c => (4208328705-1+2*2^9*c.k,106078653456026+c.lower,106079037256913+c.upper)) = pointBounds32077 := by
 decide +kernel
def cuts32078 : List PrefixCut := [⟨82,253885746,253885885⟩,
⟨128,397881416,397881636⟩]
theorem checked32078 : checkPrefixCuts (2^48) 4208459777 9 Manual.Count131072.C032078.packed 128 cuts32078 = true := by
 decide +kernel
def pointBounds32078 : List (Nat × Nat × Nat) := [(4208543744,106079303697233,106079687498485)]
theorem point_links_checked32078 : (cuts32078.take 1).map (fun c => (4208459777-1+2*2^9*c.k,106079049811487+c.lower,106079433612600+c.upper)) = pointBounds32078 := by
 decide +kernel
def cuts32079 : List PrefixCut := [⟨83,254747261,254747415⟩,
⟨128,392585523,392585753⟩]
theorem checked32079 : checkPrefixCuts (2^48) 4208590849 9 Manual.Count131072.C032079.packed 128 cuts32079 = true := by
 decide +kernel
def pointBounds32079 : List (Nat × Nat × Nat) := [(4208675840,106079702440164,106080086241651)]
theorem point_links_checked32079 : (cuts32079.take 1).map (fun c => (4208590849-1+2*2^9*c.k,106079447692903+c.lower,106079831494236+c.upper)) = pointBounds32079 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S4.B000064
