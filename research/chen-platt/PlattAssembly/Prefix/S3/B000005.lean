import PlattAssemblyKernel
import PlattCertificates.Count131072.C020160
import PlattCertificates.Count131072.C020161
import PlattCertificates.Count131072.C020162
import PlattCertificates.Count131072.C020163
import PlattCertificates.Count131072.C020164
import PlattCertificates.Count131072.C020165
import PlattCertificates.Count131072.C020166
import PlattCertificates.Count131072.C020167
import PlattCertificates.Count131072.C020168
import PlattCertificates.Count131072.C020169
import PlattCertificates.Count131072.C020170
import PlattCertificates.Count131072.C020171
import PlattCertificates.Count131072.C020172
import PlattCertificates.Count131072.C020173
import PlattCertificates.Count131072.C020174
import PlattCertificates.Count131072.C020175
import PlattCertificates.Count131072.C020176
import PlattCertificates.Count131072.C020177
import PlattCertificates.Count131072.C020178
import PlattCertificates.Count131072.C020179
import PlattCertificates.Count131072.C020180
import PlattCertificates.Count131072.C020181
import PlattCertificates.Count131072.C020182
import PlattCertificates.Count131072.C020183
import PlattCertificates.Count131072.C020184
import PlattCertificates.Count131072.C020185
import PlattCertificates.Count131072.C020186
import PlattCertificates.Count131072.C020187
import PlattCertificates.Count131072.C020188
import PlattCertificates.Count131072.C020189
import PlattCertificates.Count131072.C020190
import PlattCertificates.Count131072.C020191
namespace ChenEffective.PlattWindow.Assembly.Prefix.S3.B000005
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts20160 : List PrefixCut := [⟨25,125827639,125827713⟩,
⟨106,528935821,528936132⟩,
⟨128,644122483,644122858⟩]
theorem checked20160 : checkPrefixCuts (2^48) 2646343681 9 Manual.Count131072.C020160.packed 128 cuts20160 = true := by
 decide +kernel
def pointBounds20160 : List (Nat × Nat × Nat) := [(2646369280,100124177281241,100124557711604),(2646452224,100124580389423,100124960820023)]
theorem point_links_checked20160 : (cuts20160.take 2).map (fun c => (2646343681-1+2*2^9*c.k,100124051453602+c.lower,100124431883891+c.upper)) = pointBounds20160 := by
 decide +kernel
def cuts20161 : List PrefixCut := [⟨59,297374755,297374927⟩,
⟨128,639304708,639305082⟩]
theorem checked20161 : checkPrefixCuts (2^48) 2646474753 9 Manual.Count131072.C020161.packed 128 cuts20161 = true := by
 decide +kernel
def pointBounds20161 : List (Nat × Nat × Nat) := [(2646535168,100124992950840,100125373381676)]
theorem point_links_checked20161 : (cuts20161.take 1).map (fun c => (2646474753-1+2*2^9*c.k,100124695576085+c.lower,100125076006749+c.upper)) = pointBounds20161 := by
 decide +kernel
def cuts20162 : List PrefixCut := [⟨12,60089394,60089429⟩,
⟨93,465924810,465925077⟩,
⟨128,645015880,645016245⟩]
theorem checked20162 : checkPrefixCuts (2^48) 2646605825 9 Manual.Count131072.C020162.packed 128 cuts20162 = true := by
 decide +kernel
def pointBounds20162 : List (Nat × Nat × Nat) := [(2646618112,100125394970187,100125775401260),(2646701056,100125800805603,100126181236908)]
theorem point_links_checked20162 : (cuts20162.take 2).map (fun c => (2646605825-1+2*2^9*c.k,100125334880793+c.lower,100125715311831+c.upper)) = pointBounds20162 := by
 decide +kernel
def cuts20163 : List PrefixCut := [⟨46,234282324,234282462⟩,
⟨127,635200467,635200845⟩,
⟨128,640623942,640624323⟩]
theorem checked20163 : checkPrefixCuts (2^48) 2646736897 9 Manual.Count131072.C020163.packed 128 cuts20163 = true := by
 decide +kernel
def pointBounds20163 : List (Nat × Nat × Nat) := [(2646784000,100126214178997,100126594610538),(2646866944,100126615097140,100126995528921)]
theorem point_links_checked20163 : (cuts20163.take 2).map (fun c => (2646736897-1+2*2^9*c.k,100125979896673+c.lower,100126360328076+c.upper)) = pointBounds20163 := by
 decide +kernel
def cuts20164 : List PrefixCut := [⟨80,399735793,399736025⟩,
⟨128,640698499,640698873⟩]
theorem checked20164 : checkPrefixCuts (2^48) 2646867969 9 Manual.Count131072.C020164.packed 128 cuts20164 = true := by
 decide +kernel
def pointBounds20164 : List (Nat × Nat × Nat) := [(2646949888,100127020256408,100127400688424)]
theorem point_links_checked20164 : (cuts20164.take 1).map (fun c => (2646867969-1+2*2^9*c.k,100126620520615+c.lower,100127000952399+c.upper)) = pointBounds20164 := by
 decide +kernel
def cuts20165 : List PrefixCut := [⟨33,162801462,162801558⟩,
⟨114,566978286,566978618⟩,
⟨128,639815969,639816342⟩]
theorem checked20165 : checkPrefixCuts (2^48) 2646999041 9 Manual.Count131072.C020165.packed 128 cuts20165 = true := by
 decide +kernel
def pointBounds20165 : List (Nat × Nat × Nat) := [(2647032832,100127424020576,100127804452830),(2647115776,100127828197400,100128208629890)]
theorem point_links_checked20165 : (cuts20165.take 2).map (fun c => (2646999041-1+2*2^9*c.k,100127261219114+c.lower,100127641651272+c.upper)) = pointBounds20165 := by
 decide +kernel
def cuts20166 : List PrefixCut := [⟨67,334516466,334516667⟩,
⟨128,645951407,645951793⟩]
theorem checked20166 : checkPrefixCuts (2^48) 2647130113 9 Manual.Count131072.C020166.packed 128 cuts20166 = true := by
 decide +kernel
def pointBounds20166 : List (Nat × Nat × Nat) := [(2647198720,100128235551549,100128615984281)]
theorem point_links_checked20166 : (cuts20166.take 1).map (fun c => (2647130113-1+2*2^9*c.k,100127901035083+c.lower,100128281467614+c.upper)) = pointBounds20166 := by
 decide +kernel
def cuts20167 : List PrefixCut := [⟨20,101967037,101967095⟩,
⟨101,506637498,506637790⟩,
⟨128,641347617,641347990⟩]
theorem checked20167 : checkPrefixCuts (2^48) 2647261185 9 Manual.Count131072.C020167.packed 128 cuts20167 = true := by
 decide +kernel
def pointBounds20167 : List (Nat × Nat × Nat) := [(2647281664,100128648953527,100129029386502),(2647364608,100129053623988,100129434057197)]
theorem point_links_checked20167 : (cuts20167.take 2).map (fun c => (2647261185-1+2*2^9*c.k,100128546986490+c.lower,100128927419407+c.upper)) = pointBounds20167 := by
 decide +kernel
def cuts20168 : List PrefixCut := [⟨54,269203423,269203582⟩,
⟨128,642698009,642698387⟩]
theorem checked20168 : checkPrefixCuts (2^48) 2647392257 9 Manual.Count131072.C020168.packed 128 cuts20168 = true := by
 decide +kernel
def pointBounds20168 : List (Nat × Nat × Nat) := [(2647447552,100129457537530,100129837970979)]
theorem point_links_checked20168 : (cuts20168.take 1).map (fun c => (2647392257-1+2*2^9*c.k,100129188334107+c.lower,100129568767397+c.upper)) = pointBounds20168 := by
 decide +kernel
def cuts20169 : List PrefixCut := [⟨7,35296966,35296987⟩,
⟨88,439185126,439185384⟩,
⟨128,637563052,637563424⟩]
theorem checked20169 : checkPrefixCuts (2^48) 2647523329 9 Manual.Count131072.C020169.packed 128 cuts20169 = true := by
 decide +kernel
def pointBounds20169 : List (Nat × Nat × Nat) := [(2647530496,100129866329082,100130246762771),(2647613440,100130270217242,100130650651168)]
theorem point_links_checked20169 : (cuts20169.take 2).map (fun c => (2647523329-1+2*2^9*c.k,100129831032116+c.lower,100130211465784+c.upper)) = pointBounds20169 := by
 decide +kernel
def cuts20170 : List PrefixCut := [⟨41,211344641,211344762⟩,
⟨122,618928320,618928680⟩,
⟨128,649225500,649225879⟩]
theorem checked20170 : checkPrefixCuts (2^48) 2647654401 9 Manual.Count131072.C020170.packed 128 cuts20170 = true := by
 decide +kernel
def pointBounds20170 : List (Nat × Nat × Nat) := [(2647696384,100130679939809,100131060373970),(2647779328,100131087523488,100131467957888)]
theorem point_links_checked20170 : (cuts20170.take 2).map (fun c => (2647654401-1+2*2^9*c.k,100130468595168+c.lower,100130849029208+c.upper)) = pointBounds20170 := by
 decide +kernel
def cuts20171 : List PrefixCut := [⟨75,373021569,373021786⟩,
⟨128,641964609,641964980⟩]
theorem checked20171 : checkPrefixCuts (2^48) 2647785473 9 Manual.Count131072.C020171.packed 128 cuts20171 = true := by
 decide +kernel
def pointBounds20171 : List (Nat × Nat × Nat) := [(2647862272,100131490842237,100131871276873)]
theorem point_links_checked20171 : (cuts20171.take 1).map (fun c => (2647785473-1+2*2^9*c.k,100131117820668+c.lower,100131498255087+c.upper)) = pointBounds20171 := by
 decide +kernel
def cuts20172 : List PrefixCut := [⟨28,139359203,139359286⟩,
⟨109,549562045,549562372⟩,
⟨128,641295186,641295568⟩]
theorem checked20172 : checkPrefixCuts (2^48) 2647916545 9 Manual.Count131072.C020172.packed 128 cuts20172 = true := by
 decide +kernel
def pointBounds20172 : List (Nat × Nat × Nat) := [(2647945216,100131899144480,100132279579353),(2648028160,100132309347322,100132689782439)]
theorem point_links_checked20172 : (cuts20172.take 2).map (fun c => (2647916545-1+2*2^9*c.k,100131759785277+c.lower,100132140220067+c.upper)) = pointBounds20172 := by
 decide +kernel
def cuts20173 : List PrefixCut := [⟨62,310697281,310697464⟩,
⟨128,647534503,647534884⟩]
theorem checked20173 : checkPrefixCuts (2^48) 2648047617 9 Manual.Count131072.C020173.packed 128 cuts20173 = true := by
 decide +kernel
def pointBounds20173 : List (Nat × Nat × Nat) := [(2648111104,100132711777744,100133092213099)]
theorem point_links_checked20173 : (cuts20173.take 1).map (fun c => (2648047617-1+2*2^9*c.k,100132401080463+c.lower,100132781515635+c.upper)) = pointBounds20173 := by
 decide +kernel
def cuts20174 : List PrefixCut := [⟨15,73339883,73339925⟩,
⟨96,483078996,483079279⟩,
⟨128,643782525,643782901⟩]
theorem checked20174 : checkPrefixCuts (2^48) 2648178689 9 Manual.Count131072.C020174.packed 128 cuts20174 = true := by
 decide +kernel
def pointBounds20174 : List (Nat × Nat × Nat) := [(2648194048,100133121954849,100133502390444),(2648276992,100133531693962,100133912129798)]
theorem point_links_checked20174 : (cuts20174.take 2).map (fun c => (2648178689-1+2*2^9*c.k,100133048614966+c.lower,100133429050519+c.upper)) = pointBounds20174 := by
 decide +kernel
def cuts20175 : List PrefixCut := [⟨49,242752033,242752178⟩,
⟨128,641306148,641306527⟩]
theorem checked20175 : checkPrefixCuts (2^48) 2648309761 9 Manual.Count131072.C020175.packed 128 cuts20175 = true := by
 decide +kernel
def pointBounds20175 : List (Nat × Nat × Nat) := [(2648359936,100133935149524,100134315585598)]
theorem point_links_checked20175 : (cuts20175.take 1).map (fun c => (2648309761-1+2*2^9*c.k,100133692397491+c.lower,100134072833420+c.upper)) = pointBounds20175 := by
 decide +kernel
def cuts20176 : List PrefixCut := [⟨2,11053060,11053067⟩,
⟨83,412995335,412995580⟩,
⟨128,635960575,635960954⟩]
theorem checked20176 : checkPrefixCuts (2^48) 2648440833 9 Manual.Count131072.C020176.packed 128 cuts20176 = true := by
 decide +kernel
def pointBounds20176 : List (Nat × Nat × Nat) := [(2648442880,100134344756699,100134725193014),(2648525824,100134746698974,100135127135527)]
theorem point_links_checked20176 : (cuts20176.take 2).map (fun c => (2648440833-1+2*2^9*c.k,100134333703639+c.lower,100134714139947+c.upper)) = pointBounds20176 := by
 decide +kernel
def cuts20177 : List PrefixCut := [⟨36,176626508,176626610⟩,
⟨117,575568086,575568425⟩,
⟨128,631678214,631678585⟩]
theorem checked20177 : checkPrefixCuts (2^48) 2648571905 9 Manual.Count131072.C020177.packed 128 cuts20177 = true := by
 decide +kernel
def pointBounds20177 : List (Nat × Nat × Nat) := [(2648608768,100135146290722,100135526727511),(2648691712,100135545232300,100135925669326)]
theorem point_links_checked20177 : (cuts20177.take 2).map (fun c => (2648571905-1+2*2^9*c.k,100134969664214+c.lower,100135350100901+c.upper)) = pointBounds20177 := by
 decide +kernel
def cuts20178 : List PrefixCut := [⟨70,349620121,349620322⟩,
⟨128,636110252,636110626⟩]
theorem checked20178 : checkPrefixCuts (2^48) 2648702977 9 Manual.Count131072.C020178.packed 128 cuts20178 = true := by
 decide +kernel
def pointBounds20178 : List (Nat × Nat × Nat) := [(2648774656,100135950962549,100136331399808)]
theorem point_links_checked20178 : (cuts20178.take 1).map (fun c => (2648702977-1+2*2^9*c.k,100135601342428+c.lower,100135981779486+c.upper)) = pointBounds20178 := by
 decide +kernel
def cuts20179 : List PrefixCut := [⟨23,115189339,115189408⟩,
⟨104,526419753,526420063⟩,
⟨128,645429762,645430143⟩]
theorem checked20179 : checkPrefixCuts (2^48) 2648834049 9 Manual.Count131072.C020179.packed 128 cuts20179 = true := by
 decide +kernel
def pointBounds20179 : List (Nat × Nat × Nat) := [(2648857600,100136352642019,100136733079520),(2648940544,100136763872433,100137144310175)]
theorem point_links_checked20179 : (cuts20179.take 2).map (fun c => (2648834049-1+2*2^9*c.k,100136237452680+c.lower,100136617890112+c.upper)) = pointBounds20179 := by
 decide +kernel
def cuts20180 : List PrefixCut := [⟨57,286363349,286363512⟩,
⟨128,640616344,640616712⟩]
theorem checked20180 : checkPrefixCuts (2^48) 2648965121 9 Manual.Count131072.C020180.packed 128 cuts20180 = true := by
 decide +kernel
def pointBounds20180 : List (Nat × Nat × Nat) := [(2649023488,100137169245791,100137549683767)]
theorem point_links_checked20180 : (cuts20180.take 1).map (fun c => (2648965121-1+2*2^9*c.k,100136882882442+c.lower,100137263320255+c.upper)) = pointBounds20180 := by
 decide +kernel
def cuts20181 : List PrefixCut := [⟨10,49301380,49301408⟩,
⟨91,450611811,450612078⟩,
⟨128,632190810,632191189⟩]
theorem checked20181 : checkPrefixCuts (2^48) 2649096193 9 Manual.Count131072.C020181.packed 128 cuts20181 = true := by
 decide +kernel
def pointBounds20181 : List (Nat × Nat × Nat) := [(2649106432,100137572800166,100137953238375),(2649189376,100137974110597,100138354549045)]
theorem point_links_checked20181 : (cuts20181.take 2).map (fun c => (2649096193-1+2*2^9*c.k,100137523498786+c.lower,100137903936967+c.upper)) = pointBounds20181 := by
 decide +kernel
def cuts20182 : List PrefixCut := [⟨44,221843783,221843912⟩,
⟨125,630034972,630035348⟩,
⟨128,643952769,643953154⟩]
theorem checked20182 : checkPrefixCuts (2^48) 2649227265 9 Manual.Count131072.C020182.packed 128 cuts20182 = true := by
 decide +kernel
def pointBounds20182 : List (Nat × Nat × Nat) := [(2649272320,100138377533379,100138757972068),(2649355264,100138785724568,100139166163504)]
theorem point_links_checked20182 : (cuts20182.take 2).map (fun c => (2649227265-1+2*2^9*c.k,100138155689596+c.lower,100138536128156+c.upper)) = pointBounds20182 := by
 decide +kernel
def cuts20183 : List PrefixCut := [⟨78,393410654,393410891⟩,
⟨128,648489148,648489538⟩]
theorem checked20183 : checkPrefixCuts (2^48) 2649358337 9 Manual.Count131072.C020183.packed 128 cuts20183 = true := by
 decide +kernel
def pointBounds20183 : List (Nat × Nat × Nat) := [(2649438208,100139193053019,100139573492201)]
theorem point_links_checked20183 : (cuts20183.take 1).map (fun c => (2649358337-1+2*2^9*c.k,100138799642365+c.lower,100139180081310+c.upper)) = pointBounds20183 := by
 decide +kernel
def cuts20184 : List PrefixCut := [⟨31,156593011,156593104⟩,
⟨112,562833601,562833928⟩,
⟨128,640702023,640702396⟩]
theorem checked20184 : checkPrefixCuts (2^48) 2649489409 9 Manual.Count131072.C020184.packed 128 cuts20184 = true := by
 decide +kernel
def pointBounds20184 : List (Nat × Nat × Nat) := [(2649521152,100139604724524,100139985163952),(2649604096,100140010965114,100140391404776)]
theorem point_links_checked20184 : (cuts20184.take 2).map (fun c => (2649489409-1+2*2^9*c.k,100139448131513+c.lower,100139828570848+c.upper)) = pointBounds20184 := by
 decide +kernel
def cuts20185 : List PrefixCut := [⟨65,326234847,326235033⟩,
⟨128,638439511,638439882⟩]
theorem checked20185 : checkPrefixCuts (2^48) 2649620481 9 Manual.Count131072.C020185.packed 128 cuts20185 = true := by
 decide +kernel
def pointBounds20185 : List (Nat × Nat × Nat) := [(2649687040,100140415068383,100140795508277)]
theorem point_links_checked20185 : (cuts20185.take 1).map (fun c => (2649620481-1+2*2^9*c.k,100140088833536+c.lower,100140469273244+c.upper)) = pointBounds20185 := by
 decide +kernel
def cuts20186 : List PrefixCut := [⟨18,92098405,92098460⟩,
⟨99,500956426,500956717⟩,
⟨128,646374654,646375027⟩]
theorem checked20186 : checkPrefixCuts (2^48) 2649751553 9 Manual.Count131072.C020186.packed 128 cuts20186 = true := by
 decide +kernel
def pointBounds20186 : List (Nat × Nat × Nat) := [(2649769984,100140819371452,100141199811586),(2649852928,100141228229473,100141608669843)]
theorem point_links_checked20186 : (cuts20186.take 2).map (fun c => (2649751553-1+2*2^9*c.k,100140727273047+c.lower,100141107713126+c.upper)) = pointBounds20186 := by
 decide +kernel
def cuts20187 : List PrefixCut := [⟨52,257266269,257266424⟩,
⟨128,651547271,651547660⟩]
theorem checked20187 : checkPrefixCuts (2^48) 2649882625 9 Manual.Count131072.C020187.packed 128 cuts20187 = true := by
 decide +kernel
def pointBounds20187 : List (Nat × Nat × Nat) := [(2649935872,100141630913970,100142011354577)]
theorem point_links_checked20187 : (cuts20187.take 1).map (fun c => (2649882625-1+2*2^9*c.k,100141373647701+c.lower,100141754088153+c.upper)) = pointBounds20187 := by
 decide +kernel
def cuts20188 : List PrefixCut := [⟨5,25704340,25704356⟩,
⟨86,433355681,433355943⟩,
⟨128,642168469,642168852⟩]
theorem checked20188 : checkPrefixCuts (2^48) 2650013697 9 Manual.Count131072.C020188.packed 128 cuts20188 = true := by
 decide +kernel
def pointBounds20188 : List (Nat × Nat × Nat) := [(2650018816,100142050899312,100142431340169),(2650101760,100142458550653,100142838991756)]
theorem point_links_checked20188 : (cuts20188.take 2).map (fun c => (2650013697-1+2*2^9*c.k,100142025194972+c.lower,100142405635813+c.upper)) = pointBounds20188 := by
 decide +kernel
def cuts20189 : List PrefixCut := [⟨39,194577347,194577463⟩,
⟨120,605283176,605283532⟩,
⟨128,643835971,643836348⟩]
theorem checked20189 : checkPrefixCuts (2^48) 2650144769 9 Manual.Count131072.C020189.packed 128 cuts20189 = true := by
 decide +kernel
def pointBounds20189 : List (Nat × Nat × Nat) := [(2650184704,100142861940788,100143242382128),(2650267648,100143272646617,100143653088197)]
theorem point_links_checked20189 : (cuts20189.take 2).map (fun c => (2650144769-1+2*2^9*c.k,100142667363441+c.lower,100143047804665+c.upper)) = pointBounds20189 := by
 decide +kernel
def cuts20190 : List PrefixCut := [⟨73,369697447,369697668⟩,
⟨128,644760014,644760398⟩]
theorem checked20190 : checkPrefixCuts (2^48) 2650275841 9 Manual.Count131072.C020190.packed 128 cuts20190 = true := by
 decide +kernel
def pointBounds20190 : List (Nat × Nat × Nat) := [(2650350592,100143680896859,100144061338681)]
theorem point_links_checked20190 : (cuts20190.take 1).map (fun c => (2650275841-1+2*2^9*c.k,100143311199412+c.lower,100143691641013+c.upper)) = pointBounds20190 := by
 decide +kernel
def cuts20191 : List PrefixCut := [⟨26,129351736,129351811⟩,
⟨107,539381818,539382135⟩,
⟨128,643984693,643985071⟩]
theorem checked20191 : checkPrefixCuts (2^48) 2650406913 9 Manual.Count131072.C020191.packed 128 cuts20191 = true := by
 decide +kernel
def pointBounds20191 : List (Nat × Nat × Nat) := [(2650433536,100144085311162,100144465753222),(2650516480,100144495341244,100144875783546)]
theorem point_links_checked20191 : (cuts20191.take 2).map (fun c => (2650406913-1+2*2^9*c.k,100143955959426+c.lower,100144336401411+c.upper)) = pointBounds20191 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S3.B000005
