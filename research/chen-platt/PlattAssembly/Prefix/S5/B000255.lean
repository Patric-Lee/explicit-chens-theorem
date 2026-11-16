import PlattAssemblyKernel
import PlattCertificates.Count131072.C048160
import PlattCertificates.Count131072.C048161
import PlattCertificates.Count131072.C048162
import PlattCertificates.Count131072.C048163
import PlattCertificates.Count131072.C048164
import PlattCertificates.Count131072.C048165
import PlattCertificates.Count131072.C048166
import PlattCertificates.Count131072.C048167
import PlattCertificates.Count131072.C048168
import PlattCertificates.Count131072.C048169
import PlattCertificates.Count131072.C048170
import PlattCertificates.Count131072.C048171
import PlattCertificates.Count131072.C048172
import PlattCertificates.Count131072.C048173
import PlattCertificates.Count131072.C048174
import PlattCertificates.Count131072.C048175
import PlattCertificates.Count131072.C048176
import PlattCertificates.Count131072.C048177
import PlattCertificates.Count131072.C048178
import PlattCertificates.Count131072.C048179
import PlattCertificates.Count131072.C048180
import PlattCertificates.Count131072.C048181
import PlattCertificates.Count131072.C048182
import PlattCertificates.Count131072.C048183
import PlattCertificates.Count131072.C048184
import PlattCertificates.Count131072.C048185
import PlattCertificates.Count131072.C048186
import PlattCertificates.Count131072.C048187
import PlattCertificates.Count131072.C048188
import PlattCertificates.Count131072.C048189
import PlattCertificates.Count131072.C048190
import PlattCertificates.Count131072.C048191
namespace ChenEffective.PlattWindow.Assembly.Prefix.S5.B000255
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts48160 : List PrefixCut := [⟨45,180790100,180790202⟩,
⟨64,257927001,257927149⟩]
theorem checked48160 : checkPrefixCuts (2^48) 6316359681 10 Manual.Count131072.C048160.packed 64 cuts48160 = true := by
 decide +kernel
def pointBounds48160 : List (Nat × Nat × Nat) := [(6316451840,111190077225176,111190464080863)]
theorem point_links_checked48160 : (cuts48160.take 1).map (fun c => (6316359681-1+2*2^10*c.k,111189896435076+c.lower,111190283290661+c.upper)) = pointBounds48160 := by
 decide +kernel
def cuts48161 : List PrefixCut := [⟨64,260105188,260105337⟩]
theorem checked48161 : checkPrefixCuts (2^48) 6316490753 10 Manual.Count131072.C048161.packed 64 cuts48161 = true := by
 decide +kernel
def cuts48162 : List PrefixCut := [⟨14,56726011,56726041⟩,
⟨64,264199347,264199495⟩]
theorem checked48162 : checkPrefixCuts (2^48) 6316621825 10 Manual.Count131072.C048162.packed 64 cuts48162 = true := by
 decide +kernel
def pointBounds48162 : List (Nat × Nat × Nat) := [(6316650496,111190471193276,111190858049188)]
theorem point_links_checked48162 : (cuts48162.take 1).map (fun c => (6316621825-1+2*2^10*c.k,111190414467265+c.lower,111190801323147+c.upper)) = pointBounds48162 := by
 decide +kernel
def cuts48163 : List PrefixCut := [⟨47,192408876,192408984⟩,
⟨64,259960713,259960859⟩]
theorem checked48163 : checkPrefixCuts (2^48) 6316752897 10 Manual.Count131072.C048163.packed 64 cuts48163 = true := by
 decide +kernel
def pointBounds48163 : List (Nat × Nat × Nat) := [(6316849152,111190871075488,111191257931626)]
theorem point_links_checked48163 : (cuts48163.take 1).map (fun c => (6316752897-1+2*2^10*c.k,111190678666612+c.lower,111191065522642+c.upper)) = pointBounds48163 := by
 decide +kernel
def cuts48164 : List PrefixCut := [⟨64,255499411,255499553⟩]
theorem checked48164 : checkPrefixCuts (2^48) 6316883969 10 Manual.Count131072.C048164.packed 64 cuts48164 = true := by
 decide +kernel
def cuts48165 : List PrefixCut := [⟨16,64163658,64163695⟩,
⟨64,258033923,258034068⟩]
theorem checked48165 : checkPrefixCuts (2^48) 6317015041 10 Manual.Count131072.C048165.packed 64 cuts48165 = true := by
 decide +kernel
def pointBounds48165 : List (Nat × Nat × Nat) := [(6317047808,111191258290394,111191645146749)]
theorem point_links_checked48165 : (cuts48165.take 1).map (fun c => (6317015041-1+2*2^10*c.k,111191194126736+c.lower,111191580983054+c.upper)) = pointBounds48165 := by
 decide +kernel
def cuts48166 : List PrefixCut := [⟨49,196139625,196139738⟩,
⟨64,256914651,256914799⟩]
theorem checked48166 : checkPrefixCuts (2^48) 6317146113 10 Manual.Count131072.C048166.packed 64 cuts48166 = true := by
 decide +kernel
def pointBounds48166 : List (Nat × Nat × Nat) := [(6317246464,111191648300284,111192035156860)]
theorem point_links_checked48166 : (cuts48166.take 1).map (fun c => (6317146113-1+2*2^10*c.k,111191452160659+c.lower,111191839017122+c.upper)) = pointBounds48166 := by
 decide +kernel
def cuts48167 : List PrefixCut := [⟨64,259226231,259226382⟩]
theorem checked48167 : checkPrefixCuts (2^48) 6317277185 10 Manual.Count131072.C048167.packed 64 cuts48167 = true := by
 decide +kernel
def cuts48168 : List PrefixCut := [⟨18,73739039,73739077⟩,
⟨64,261314942,261315084⟩]
theorem checked48168 : checkPrefixCuts (2^48) 6317408257 10 Manual.Count131072.C048168.packed 64 cuts48168 = true := by
 decide +kernel
def pointBounds48168 : List (Nat × Nat × Nat) := [(6317445120,111192042040580,111192428897380)]
theorem point_links_checked48168 : (cuts48168.take 1).map (fun c => (6317408257-1+2*2^10*c.k,111191968301541+c.lower,111192355158303+c.upper)) = pointBounds48168 := by
 decide +kernel
def cuts48169 : List PrefixCut := [⟨51,205350071,205350189⟩,
⟨64,258146185,258146333⟩]
theorem checked48169 : checkPrefixCuts (2^48) 6317539329 10 Manual.Count131072.C048169.packed 64 cuts48169 = true := by
 decide +kernel
def pointBounds48169 : List (Nat × Nat × Nat) := [(6317643776,111192434966554,111192821823576)]
theorem point_links_checked48169 : (cuts48169.take 1).map (fun c => (6317539329-1+2*2^10*c.k,111192229616483+c.lower,111192616473387+c.upper)) = pointBounds48169 := by
 decide +kernel
def cuts48170 : List PrefixCut := [⟨64,264066400,264066549⟩]
theorem checked48170 : checkPrefixCuts (2^48) 6317670401 10 Manual.Count131072.C048170.packed 64 cuts48170 = true := by
 decide +kernel
def cuts48171 : List PrefixCut := [⟨20,79838124,79838168⟩,
⟨64,257155318,257155464⟩]
theorem checked48171 : checkPrefixCuts (2^48) 6317801473 10 Manual.Count131072.C048171.packed 64 cuts48171 = true := by
 decide +kernel
def pointBounds48171 : List (Nat × Nat × Nat) := [(6317842432,111192831667192,111193218524437)]
theorem point_links_checked48171 : (cuts48171.take 1).map (fun c => (6317801473-1+2*2^10*c.k,111192751829068+c.lower,111193138686269+c.upper)) = pointBounds48171 := by
 decide +kernel
def cuts48172 : List PrefixCut := [⟨53,208901330,208901448⟩,
⟨64,252516659,252516801⟩]
theorem checked48172 : checkPrefixCuts (2^48) 6317932545 10 Manual.Count131072.C048172.packed 64 cuts48172 = true := by
 decide +kernel
def pointBounds48172 : List (Nat × Nat × Nat) := [(6318041088,111193217885716,111193604743181)]
theorem point_links_checked48172 : (cuts48172.take 1).map (fun c => (6317932545-1+2*2^10*c.k,111193008984386+c.lower,111193395841733+c.upper)) = pointBounds48172 := by
 decide +kernel
def cuts48173 : List PrefixCut := [⟨64,258392064,258392214⟩]
theorem checked48173 : checkPrefixCuts (2^48) 6318063617 10 Manual.Count131072.C048173.packed 64 cuts48173 = true := by
 decide +kernel
def cuts48174 : List PrefixCut := [⟨22,86560130,86560179⟩,
⟨64,258208475,258208628⟩]
theorem checked48174 : checkPrefixCuts (2^48) 6318194689 10 Manual.Count131072.C048174.packed 64 cuts48174 = true := by
 decide +kernel
def pointBounds48174 : List (Nat × Nat × Nat) := [(6318239744,111193606453239,111193993310927)]
theorem point_links_checked48174 : (cuts48174.take 1).map (fun c => (6318194689-1+2*2^10*c.k,111193519893109+c.lower,111193906750748+c.upper)) = pointBounds48174 := by
 decide +kernel
def cuts48175 : List PrefixCut := [⟨55,226841318,226841449⟩,
⟨64,263370768,263370919⟩]
theorem checked48175 : checkPrefixCuts (2^48) 6318325761 10 Manual.Count131072.C048175.packed 64 cuts48175 = true := by
 decide +kernel
def pointBounds48175 : List (Nat × Nat × Nat) := [(6318438400,111194004942902,111194391800825)]
theorem point_links_checked48175 : (cuts48175.take 1).map (fun c => (6318325761-1+2*2^10*c.k,111193778101584+c.lower,111194164959376+c.upper)) = pointBounds48175 := by
 decide +kernel
def cuts48176 : List PrefixCut := [⟨64,260068797,260068945⟩]
theorem checked48176 : checkPrefixCuts (2^48) 6318456833 10 Manual.Count131072.C048176.packed 64 cuts48176 = true := by
 decide +kernel
def cuts48177 : List PrefixCut := [⟨24,95998667,95998723⟩,
⟨64,259840644,259840794⟩]
theorem checked48177 : checkPrefixCuts (2^48) 6318587905 10 Manual.Count131072.C048177.packed 64 cuts48177 = true := by
 decide +kernel
def pointBounds48177 : List (Nat × Nat × Nat) := [(6318637056,111194397539816,111194784397963)]
theorem point_links_checked48177 : (cuts48177.take 1).map (fun c => (6318587905-1+2*2^10*c.k,111194301541149+c.lower,111194688399240+c.upper)) = pointBounds48177 := by
 decide +kernel
def cuts48178 : List PrefixCut := [⟨57,231058973,231059108⟩,
⟨64,259389798,259389949⟩]
theorem checked48178 : checkPrefixCuts (2^48) 6318718977 10 Manual.Count131072.C048178.packed 64 cuts48178 = true := by
 decide +kernel
def pointBounds48178 : List (Nat × Nat × Nat) := [(6318835712,111194792440766,111195179299142)]
theorem point_links_checked48178 : (cuts48178.take 1).map (fun c => (6318718977-1+2*2^10*c.k,111194561381793+c.lower,111194948240034+c.upper)) = pointBounds48178 := by
 decide +kernel
def cuts48179 : List PrefixCut := [⟨64,259428969,259429118⟩]
theorem checked48179 : checkPrefixCuts (2^48) 6318850049 10 Manual.Count131072.C048179.packed 64 cuts48179 = true := by
 decide +kernel
def cuts48180 : List PrefixCut := [⟨26,105525118,105525180⟩,
⟨64,259690861,259691013⟩]
theorem checked48180 : checkPrefixCuts (2^48) 6318981121 10 Manual.Count131072.C048180.packed 64 cuts48180 = true := by
 decide +kernel
def pointBounds48180 : List (Nat × Nat × Nat) := [(6319034368,111195185725678,111195572584281)]
theorem point_links_checked48180 : (cuts48180.take 1).map (fun c => (6318981121-1+2*2^10*c.k,111195080200560+c.lower,111195467059101+c.upper)) = pointBounds48180 := by
 decide +kernel
def cuts48181 : List PrefixCut := [⟨59,238082331,238082467⟩,
⟨64,258126472,258126620⟩]
theorem checked48181 : checkPrefixCuts (2^48) 6319112193 10 Manual.Count131072.C048181.packed 64 cuts48181 = true := by
 decide +kernel
def pointBounds48181 : List (Nat × Nat × Nat) := [(6319233024,111195577973752,111195964832581)]
theorem point_links_checked48181 : (cuts48181.take 1).map (fun c => (6319112193-1+2*2^10*c.k,111195339891421+c.lower,111195726750114+c.upper)) = pointBounds48181 := by
 decide +kernel
def cuts48182 : List PrefixCut := [⟨64,260704531,260704677⟩]
theorem checked48182 : checkPrefixCuts (2^48) 6319243265 10 Manual.Count131072.C048182.packed 64 cuts48182 = true := by
 decide +kernel
def cuts48183 : List PrefixCut := [⟨28,114694041,114694109⟩,
⟨64,261634516,261634659⟩]
theorem checked48183 : checkPrefixCuts (2^48) 6319374337 10 Manual.Count131072.C048183.packed 64 cuts48183 = true := by
 decide +kernel
def pointBounds48183 : List (Nat × Nat × Nat) := [(6319431680,111195973416465,111196360275520)]
theorem point_links_checked48183 : (cuts48183.take 1).map (fun c => (6319374337-1+2*2^10*c.k,111195858722424+c.lower,111196245581411+c.upper)) = pointBounds48183 := by
 decide +kernel
def cuts48184 : List PrefixCut := [⟨61,245282944,245283087⟩,
⟨64,257041438,257041588⟩]
theorem checked48184 : checkPrefixCuts (2^48) 6319505409 10 Manual.Count131072.C048184.packed 64 cuts48184 = true := by
 decide +kernel
def pointBounds48184 : List (Nat × Nat × Nat) := [(6319630336,111196365639884,111196752499157)]
theorem point_links_checked48184 : (cuts48184.take 1).map (fun c => (6319505409-1+2*2^10*c.k,111196120356940+c.lower,111196507216070+c.upper)) = pointBounds48184 := by
 decide +kernel
def cuts48185 : List PrefixCut := [⟨64,262781655,262781806⟩]
theorem checked48185 : checkPrefixCuts (2^48) 6319636481 10 Manual.Count131072.C048185.packed 64 cuts48185 = true := by
 decide +kernel
def cuts48186 : List PrefixCut := [⟨30,121723970,121724042⟩,
⟨64,258099721,258099869⟩]
theorem checked48186 : checkPrefixCuts (2^48) 6319767553 10 Manual.Count131072.C048186.packed 64 cuts48186 = true := by
 decide +kernel
def pointBounds48186 : List (Nat × Nat × Nat) := [(6319828992,111196761904003,111197148763506)]
theorem point_links_checked48186 : (cuts48186.take 1).map (fun c => (6319767553-1+2*2^10*c.k,111196640180033+c.lower,111197027039464+c.upper)) = pointBounds48186 := by
 decide +kernel
def cuts48187 : List PrefixCut := [⟨63,253417960,253418101⟩,
⟨64,257159065,257159208⟩]
theorem checked48187 : checkPrefixCuts (2^48) 6319898625 10 Manual.Count131072.C048187.packed 64 cuts48187 = true := by
 decide +kernel
def pointBounds48187 : List (Nat × Nat × Nat) := [(6320027648,111197151697714,111197538557434)]
theorem point_links_checked48187 : (cuts48187.take 1).map (fun c => (6319898625-1+2*2^10*c.k,111196898279754+c.lower,111197285139333+c.upper)) = pointBounds48187 := by
 decide +kernel
def cuts48188 : List PrefixCut := [⟨64,261295597,261295750⟩]
theorem checked48188 : checkPrefixCuts (2^48) 6320029697 10 Manual.Count131072.C048188.packed 64 cuts48188 = true := by
 decide +kernel
def cuts48189 : List PrefixCut := [⟨32,126927042,126927117⟩,
⟨64,258439904,258440052⟩]
theorem checked48189 : checkPrefixCuts (2^48) 6320160769 10 Manual.Count131072.C048189.packed 64 cuts48189 = true := by
 decide +kernel
def pointBounds48189 : List (Nat × Nat × Nat) := [(6320226304,111197543661458,111197930521408)]
theorem point_links_checked48189 : (cuts48189.take 1).map (fun c => (6320160769-1+2*2^10*c.k,111197416734416+c.lower,111197803594291+c.upper)) = pointBounds48189 := by
 decide +kernel
def cuts48190 : List PrefixCut := [⟨64,253802968,253803114⟩]
theorem checked48190 : checkPrefixCuts (2^48) 6320291841 10 Manual.Count131072.C048190.packed 64 cuts48190 = true := by
 decide +kernel
def cuts48191 : List PrefixCut := [⟨1,4186213,4186215⟩,
⟨64,261546570,261546716⟩]
theorem checked48191 : checkPrefixCuts (2^48) 6320422913 10 Manual.Count131072.C048191.packed 64 cuts48191 = true := by
 decide +kernel
def pointBounds48191 : List (Nat × Nat × Nat) := [(6320424960,111197933163501,111198320023672)]
theorem point_links_checked48191 : (cuts48191.take 1).map (fun c => (6320422913-1+2*2^10*c.k,111197928977288+c.lower,111198315837457+c.upper)) = pointBounds48191 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S5.B000255
