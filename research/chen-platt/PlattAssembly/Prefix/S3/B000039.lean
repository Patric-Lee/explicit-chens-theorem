import PlattAssemblyKernel
import PlattCertificates.Count131072.C021248
import PlattCertificates.Count131072.C021249
import PlattCertificates.Count131072.C021250
import PlattCertificates.Count131072.C021251
import PlattCertificates.Count131072.C021252
import PlattCertificates.Count131072.C021253
import PlattCertificates.Count131072.C021254
import PlattCertificates.Count131072.C021255
import PlattCertificates.Count131072.C021256
import PlattCertificates.Count131072.C021257
import PlattCertificates.Count131072.C021258
import PlattCertificates.Count131072.C021259
import PlattCertificates.Count131072.C021260
import PlattCertificates.Count131072.C021261
import PlattCertificates.Count131072.C021262
import PlattCertificates.Count131072.C021263
import PlattCertificates.Count131072.C021264
import PlattCertificates.Count131072.C021265
import PlattCertificates.Count131072.C021266
import PlattCertificates.Count131072.C021267
import PlattCertificates.Count131072.C021268
import PlattCertificates.Count131072.C021269
import PlattCertificates.Count131072.C021270
import PlattCertificates.Count131072.C021271
import PlattCertificates.Count131072.C021272
import PlattCertificates.Count131072.C021273
import PlattCertificates.Count131072.C021274
import PlattCertificates.Count131072.C021275
import PlattCertificates.Count131072.C021276
import PlattCertificates.Count131072.C021277
import PlattCertificates.Count131072.C021278
import PlattCertificates.Count131072.C021279
namespace ChenEffective.PlattWindow.Assembly.Prefix.S3.B000039
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts21248 : List PrefixCut := [⟨48,230409841,230409976⟩,
⟨128,615628238,615628593⟩]
theorem checked21248 : checkPrefixCuts (2^48) 2788950017 9 Manual.Count131072.C021248.packed 128 cuts21248 = true := by
 decide +kernel
def pointBounds21248 : List (Nat × Nat × Nat) := [(2788999168,100804329489804,100804710315865)]
theorem point_links_checked21248 : (cuts21248.take 1).map (fun c => (2788950017-1+2*2^9*c.k,100804099079963+c.lower,100804479905889+c.upper)) = pointBounds21248 := by
 decide +kernel
def cuts21249 : List PrefixCut := [⟨6,28459492,28459509⟩,
⟨92,433849072,433849326⟩,
⟨128,606213968,606214323⟩]
theorem checked21249 : checkPrefixCuts (2^48) 2789081089 9 Manual.Count131072.C021249.packed 128 cuts21249 = true := by
 decide +kernel
def pointBounds21249 : List (Nat × Nat × Nat) := [(2789087232,100804743167693,100805123993991),(2789175296,100805148557273,100805529383808)]
theorem point_links_checked21249 : (cuts21249.take 2).map (fun c => (2789081089-1+2*2^9*c.k,100804714708201+c.lower,100805095534482+c.upper)) = pointBounds21249 := by
 decide +kernel
def cuts21250 : List PrefixCut := [⟨50,239773174,239773319⟩,
⟨128,610423800,610424163⟩]
theorem checked21250 : checkPrefixCuts (2^48) 2789212161 9 Manual.Count131072.C021250.packed 128 cuts21250 = true := by
 decide +kernel
def pointBounds21250 : List (Nat × Nat × Nat) := [(2789263360,100805560695343,100805941522124)]
theorem point_links_checked21250 : (cuts21250.take 1).map (fun c => (2789212161-1+2*2^9*c.k,100805320922169+c.lower,100805701748805+c.upper)) = pointBounds21250 := by
 decide +kernel
def cuts21251 : List PrefixCut := [⟨8,36731483,36731506⟩,
⟨94,448238045,448238307⟩,
⟨128,603634338,603634691⟩]
theorem checked21251 : checkPrefixCuts (2^48) 2789343233 9 Manual.Count131072.C021251.packed 128 cuts21251 = true := by
 decide +kernel
def pointBounds21251 : List (Nat × Nat × Nat) := [(2789351424,100805968077452,100806348904474),(2789439488,100806379584014,100806760411275)]
theorem point_links_checked21251 : (cuts21251.take 2).map (fun c => (2789343233-1+2*2^9*c.k,100805931345969+c.lower,100806312172968+c.upper)) = pointBounds21251 := by
 decide +kernel
def cuts21252 : List PrefixCut := [⟨52,247116602,247116743⟩,
⟨128,606733938,606734288⟩]
theorem checked21252 : checkPrefixCuts (2^48) 2789474305 9 Manual.Count131072.C021252.packed 128 cuts21252 = true := by
 decide +kernel
def pointBounds21252 : List (Nat × Nat × Nat) := [(2789527552,100806782096909,100807162924402)]
theorem point_links_checked21252 : (cuts21252.take 1).map (fun c => (2789474305-1+2*2^9*c.k,100806534980307+c.lower,100806915807659+c.upper)) = pointBounds21252 := by
 decide +kernel
def cuts21253 : List PrefixCut := [⟨10,49037956,49037984⟩,
⟨96,450012106,450012363⟩,
⟨128,601055168,601055517⟩]
theorem checked21253 : checkPrefixCuts (2^48) 2789605377 9 Manual.Count131072.C021253.packed 128 cuts21253 = true := by
 decide +kernel
def pointBounds21253 : List (Nat × Nat × Nat) := [(2789615616,100807190752201,100807571579931),(2789703680,100807591726351,100807972554310)]
theorem point_links_checked21253 : (cuts21253.take 2).map (fun c => (2789605377-1+2*2^9*c.k,100807141714245+c.lower,100807522541947+c.upper)) = pointBounds21253 := by
 decide +kernel
def cuts21254 : List PrefixCut := [⟨54,260613313,260613460⟩,
⟨128,615757472,615757825⟩]
theorem checked21254 : checkPrefixCuts (2^48) 2789736449 9 Manual.Count131072.C021254.packed 128 cuts21254 = true := by
 decide +kernel
def pointBounds21254 : List (Nat × Nat × Nat) := [(2789791744,100808003382726,100808384210924)]
theorem point_links_checked21254 : (cuts21254.take 1).map (fun c => (2789736449-1+2*2^9*c.k,100807742769413+c.lower,100808123597464+c.upper)) = pointBounds21254 := by
 decide +kernel
def cuts21255 : List PrefixCut := [⟨12,54380588,54380621⟩,
⟨98,466010979,466011250⟩,
⟨128,610179457,610179810⟩]
theorem checked21255 : checkPrefixCuts (2^48) 2789867521 9 Manual.Count131072.C021255.packed 128 cuts21255 = true := by
 decide +kernel
def pointBounds21255 : List (Nat × Nat × Nat) := [(2789879808,100808412907473,100808793735910),(2789967872,100808824537864,100809205366539)]
theorem point_links_checked21255 : (cuts21255.take 2).map (fun c => (2789867521-1+2*2^9*c.k,100808358526885+c.lower,100808739355289+c.upper)) = pointBounds21255 := by
 decide +kernel
def cuts21256 : List PrefixCut := [⟨56,265027748,265027899⟩,
⟨128,605611169,605611519⟩]
theorem checked21256 : checkPrefixCuts (2^48) 2789998593 9 Manual.Count131072.C021256.packed 128 cuts21256 = true := by
 decide +kernel
def pointBounds21256 : List (Nat × Nat × Nat) := [(2790055936,100809233734090,100809614562998)]
theorem point_links_checked21256 : (cuts21256.take 1).map (fun c => (2789998593-1+2*2^9*c.k,100808968706342+c.lower,100809349535099+c.upper)) = pointBounds21256 := by
 decide +kernel
def cuts21257 : List PrefixCut := [⟨14,64564548,64564585⟩,
⟨100,473129585,473129859⟩,
⟨128,601950976,601951326⟩]
theorem checked21257 : checkPrefixCuts (2^48) 2790129665 9 Manual.Count131072.C021257.packed 128 cuts21257 = true := by
 decide +kernel
def pointBounds21257 : List (Nat × Nat × Nat) := [(2790144000,100809638882059,100810019711203),(2790232064,100810047447096,100810428276477)]
theorem point_links_checked21257 : (cuts21257.take 2).map (fun c => (2790129665-1+2*2^9*c.k,100809574317511+c.lower,100809955146618+c.upper)) = pointBounds21257 := by
 decide +kernel
def cuts21258 : List PrefixCut := [⟨58,276200028,276200187⟩,
⟨128,603435900,603436249⟩]
theorem checked21258 : checkPrefixCuts (2^48) 2790260737 9 Manual.Count131072.C021258.packed 128 cuts21258 = true := by
 decide +kernel
def pointBounds21258 : List (Nat × Nat × Nat) := [(2790320128,100810452468515,100810833298131)]
theorem point_links_checked21258 : (cuts21258.take 1).map (fun c => (2790260737-1+2*2^9*c.k,100810176268487+c.lower,100810557097944+c.upper)) = pointBounds21258 := by
 decide +kernel
def cuts21259 : List PrefixCut := [⟨16,75654451,75654497⟩,
⟨102,490434835,490435126⟩,
⟨128,613595425,613595787⟩]
theorem checked21259 : checkPrefixCuts (2^48) 2790391809 9 Manual.Count131072.C021259.packed 128 cuts21259 = true := by
 decide +kernel
def pointBounds21259 : List (Nat × Nat × Nat) := [(2790408192,100810855358838,100811236188690),(2790496256,100811270139222,100811650969319)]
theorem point_links_checked21259 : (cuts21259.take 2).map (fun c => (2790391809-1+2*2^9*c.k,100810779704387+c.lower,100811160534193+c.upper)) = pointBounds21259 := by
 decide +kernel
def cuts21260 : List PrefixCut := [⟨60,282225976,282226141⟩,
⟨128,603984268,603984616⟩]
theorem checked21260 : checkPrefixCuts (2^48) 2790522881 9 Manual.Count131072.C021260.packed 128 cuts21260 = true := by
 decide +kernel
def pointBounds21260 : List (Nat × Nat × Nat) := [(2790584320,100811675525788,100812056356121)]
theorem point_links_checked21260 : (cuts21260.take 1).map (fun c => (2790522881-1+2*2^9*c.k,100811393299812+c.lower,100811774129980+c.upper)) = pointBounds21260 := by
 decide +kernel
def cuts21261 : List PrefixCut := [⟨18,86338805,86338857⟩,
⟨104,492506696,492506986⟩,
⟨128,603048292,603048650⟩]
theorem checked21261 : checkPrefixCuts (2^48) 2790653953 9 Manual.Count131072.C021261.packed 128 cuts21261 = true := by
 decide +kernel
def pointBounds21261 : List (Nat × Nat × Nat) := [(2790672384,100812083622885,100812464453453),(2790760448,100812489790776,100812870621582)]
theorem point_links_checked21261 : (cuts21261.take 2).map (fun c => (2790653953-1+2*2^9*c.k,100811997284080+c.lower,100812378114596+c.upper)) = pointBounds21261 := by
 decide +kernel
def cuts21262 : List PrefixCut := [⟨62,296319435,296319607⟩,
⟨128,612298699,612299053⟩]
theorem checked21262 : checkPrefixCuts (2^48) 2790785025 9 Manual.Count131072.C021262.packed 128 cuts21262 = true := by
 decide +kernel
def pointBounds21262 : List (Nat × Nat × Nat) := [(2790848512,100812896651807,100813277482853)]
theorem point_links_checked21262 : (cuts21262.take 1).map (fun c => (2790785025-1+2*2^9*c.k,100812600332372+c.lower,100812981163246+c.upper)) = pointBounds21262 := by
 decide +kernel
def cuts21263 : List PrefixCut := [⟨20,97323706,97323759⟩,
⟨106,507386403,507386693⟩,
⟨128,610757263,610757615⟩]
theorem checked21263 : checkPrefixCuts (2^48) 2790916097 9 Manual.Count131072.C021263.packed 128 cuts21263 = true := by
 decide +kernel
def pointBounds21263 : List (Nat × Nat × Nat) := [(2790936576,100813309954777,100813690786058),(2791024640,100813720017474,100814100848992)]
theorem point_links_checked21263 : (cuts21263.take 2).map (fun c => (2790916097-1+2*2^9*c.k,100813212631071+c.lower,100813593462299+c.upper)) = pointBounds21263 := by
 decide +kernel
def cuts21264 : List PrefixCut := [⟨64,296896596,296896774⟩,
⟨128,606492720,606493079⟩]
theorem checked21264 : checkPrefixCuts (2^48) 2791047169 9 Manual.Count131072.C021264.packed 128 cuts21264 = true := by
 decide +kernel
def pointBounds21264 : List (Nat × Nat × Nat) := [(2791112704,100814120284930,100814501116688)]
theorem point_links_checked21264 : (cuts21264.take 1).map (fun c => (2791047169-1+2*2^9*c.k,100813823388334+c.lower,100814204219914+c.upper)) = pointBounds21264 := by
 decide +kernel
def cuts21265 : List PrefixCut := [⟨22,105583738,105583798⟩,
⟨108,515405881,515406173⟩,
⟨128,609993908,609994253⟩]
theorem checked21265 : checkPrefixCuts (2^48) 2791178241 9 Manual.Count131072.C021265.packed 128 cuts21265 = true := by
 decide +kernel
def pointBounds21265 : List (Nat × Nat × Nat) := [(2791200768,100814535464792,100814916296791),(2791288832,100814945286935,100815326119166)]
theorem point_links_checked21265 : (cuts21265.take 2).map (fun c => (2791178241-1+2*2^9*c.k,100814429881054+c.lower,100814810712993+c.upper)) = pointBounds21265 := by
 decide +kernel
def cuts21266 : List PrefixCut := [⟨66,320969029,320969215⟩,
⟨128,616721429,616721792⟩]
theorem checked21266 : checkPrefixCuts (2^48) 2791309313 9 Manual.Count131072.C021266.packed 128 cuts21266 = true := by
 decide +kernel
def pointBounds21266 : List (Nat × Nat × Nat) := [(2791376896,100815360843991,100815741676461)]
theorem point_links_checked21266 : (cuts21266.take 1).map (fun c => (2791309313-1+2*2^9*c.k,100815039874962+c.lower,100815420707246+c.upper)) = pointBounds21266 := by
 decide +kernel
def cuts21267 : List PrefixCut := [⟨24,112430537,112430599⟩,
⟨110,521508131,521508427⟩,
⟨128,607214140,607214486⟩]
theorem checked21267 : checkPrefixCuts (2^48) 2791440385 9 Manual.Count131072.C021267.packed 128 cuts21267 = true := by
 decide +kernel
def pointBounds21267 : List (Nat × Nat × Nat) := [(2791464960,100815769026928,100816149859637),(2791553024,100816178104522,100816558937465)]
theorem point_links_checked21267 : (cuts21267.take 2).map (fun c => (2791440385-1+2*2^9*c.k,100815656596391+c.lower,100816037429038+c.upper)) = pointBounds21267 := by
 decide +kernel
def cuts21268 : List PrefixCut := [⟨68,324467714,324467899⟩,
⟨128,602043482,602043834⟩]
theorem checked21268 : checkPrefixCuts (2^48) 2791571457 9 Manual.Count131072.C021268.packed 128 cuts21268 = true := by
 decide +kernel
def pointBounds21268 : List (Nat × Nat × Nat) := [(2791641088,100816588278245,100816969111423)]
theorem point_links_checked21268 : (cuts21268.take 1).map (fun c => (2791571457-1+2*2^9*c.k,100816263810531+c.lower,100816644643524+c.upper)) = pointBounds21268 := by
 decide +kernel
def cuts21269 : List PrefixCut := [⟨26,119376871,119376940⟩,
⟨112,528113223,528113531⟩,
⟨128,600401947,600402299⟩]
theorem checked21269 : checkPrefixCuts (2^48) 2791702529 9 Manual.Count131072.C021269.packed 128 cuts21269 = true := by
 decide +kernel
def pointBounds21269 : List (Nat × Nat × Nat) := [(2791729152,100816985230884,100817366064298),(2791817216,100817393967236,100817774800889)]
theorem point_links_checked21269 : (cuts21269.take 2).map (fun c => (2791702529-1+2*2^9*c.k,100816865854013+c.lower,100817246687358+c.upper)) = pointBounds21269 := by
 decide +kernel
def cuts21270 : List PrefixCut := [⟨70,337947007,337947201⟩,
⟨128,609044274,609044625⟩]
theorem checked21270 : checkPrefixCuts (2^48) 2791833601 9 Manual.Count131072.C021270.packed 128 cuts21270 = true := by
 decide +kernel
def pointBounds21270 : List (Nat × Nat × Nat) := [(2791905280,100817804202967,100818185036858)]
theorem point_links_checked21270 : (cuts21270.take 1).map (fun c => (2791833601-1+2*2^9*c.k,100817466255960+c.lower,100817847089657+c.upper)) = pointBounds21270 := by
 decide +kernel
def cuts21271 : List PrefixCut := [⟨28,134387119,134387199⟩,
⟨114,542984072,542984390⟩,
⟨128,609418911,609419265⟩]
theorem checked21271 : checkPrefixCuts (2^48) 2791964673 9 Manual.Count131072.C021271.packed 128 cuts21271 = true := by
 decide +kernel
def pointBounds21271 : List (Nat × Nat × Nat) := [(2791993344,100818209687353,100818590521481),(2792081408,100818618284306,100818999118672)]
theorem point_links_checked21271 : (cuts21271.take 2).map (fun c => (2791964673-1+2*2^9*c.k,100818075300234+c.lower,100818456134282+c.upper)) = pointBounds21271 := by
 decide +kernel
def cuts21272 : List PrefixCut := [⟨72,343056394,343056593⟩,
⟨128,606769180,606769532⟩]
theorem checked21272 : checkPrefixCuts (2^48) 2792095745 9 Manual.Count131072.C021272.packed 128 cuts21272 = true := by
 decide +kernel
def pointBounds21272 : List (Nat × Nat × Nat) := [(2792169472,100819027775539,100819408610140)]
theorem point_links_checked21272 : (cuts21272.take 1).map (fun c => (2792095745-1+2*2^9*c.k,100818684719145+c.lower,100819065553547+c.upper)) = pointBounds21272 := by
 decide +kernel
def cuts21273 : List PrefixCut := [⟨30,139011531,139011614⟩,
⟨116,552005096,552005418⟩,
⟨128,612083144,612083501⟩]
theorem checked21273 : checkPrefixCuts (2^48) 2792226817 9 Manual.Count131072.C021273.packed 128 cuts21273 = true := by
 decide +kernel
def pointBounds21273 : List (Nat × Nat × Nat) := [(2792257536,100819430499856,100819811334693),(2792345600,100819843493421,100820224328497)]
theorem point_links_checked21273 : (cuts21273.take 2).map (fun c => (2792226817-1+2*2^9*c.k,100819291488325+c.lower,100819672323079+c.upper)) = pointBounds21273 := by
 decide +kernel
def cuts21274 : List PrefixCut := [⟨74,352700959,352701163⟩,
⟨128,606208306,606208660⟩]
theorem checked21274 : checkPrefixCuts (2^48) 2792357889 9 Manual.Count131072.C021274.packed 128 cuts21274 = true := by
 decide +kernel
def pointBounds21274 : List (Nat × Nat × Nat) := [(2792433664,100820256272428,100820637107743)]
theorem point_links_checked21274 : (cuts21274.take 1).map (fun c => (2792357889-1+2*2^9*c.k,100819903571469+c.lower,100820284406580+c.upper)) = pointBounds21274 := by
 decide +kernel
def cuts21275 : List PrefixCut := [⟨32,153613950,153614038⟩,
⟨118,556186708,556187032⟩,
⟨128,602450507,602450858⟩]
theorem checked21275 : checkPrefixCuts (2^48) 2792488961 9 Manual.Count131072.C021275.packed 128 cuts21275 = true := by
 decide +kernel
def pointBounds21275 : List (Nat × Nat × Nat) := [(2792521728,100820663393725,100821044229278),(2792609792,100821065966483,100821446802272)]
theorem point_links_checked21275 : (cuts21275.take 2).map (fun c => (2792488961-1+2*2^9*c.k,100820509779775+c.lower,100820890615240+c.upper)) = pointBounds21275 := by
 decide +kernel
def cuts21276 : List PrefixCut := [⟨76,362142073,362142285⟩,
⟨128,607763959,607764315⟩]
theorem checked21276 : checkPrefixCuts (2^48) 2792620033 9 Manual.Count131072.C021276.packed 128 cuts21276 = true := by
 decide +kernel
def pointBounds21276 : List (Nat × Nat × Nat) := [(2792697856,100821474372355,100821855208383)]
theorem point_links_checked21276 : (cuts21276.take 1).map (fun c => (2792620033-1+2*2^9*c.k,100821112230282+c.lower,100821493066098+c.upper)) = pointBounds21276 := by
 decide +kernel
def cuts21277 : List PrefixCut := [⟨34,161662436,161662528⟩,
⟨120,568530733,568531057⟩,
⟨128,605316563,605316908⟩]
theorem checked21277 : checkPrefixCuts (2^48) 2792751105 9 Manual.Count131072.C021277.packed 128 cuts21277 = true := by
 decide +kernel
def pointBounds21277 : List (Nat × Nat × Nat) := [(2792785920,100821881656677,100822262492941),(2792873984,100822288524974,100822669361470)]
theorem point_links_checked21277 : (cuts21277.take 2).map (fun c => (2792751105-1+2*2^9*c.k,100821719994241+c.lower,100822100830413+c.upper)) = pointBounds21277 := by
 decide +kernel
def cuts21278 : List PrefixCut := [⟨78,371783000,371783212⟩,
⟨128,609420241,609420584⟩]
theorem checked21278 : checkPrefixCuts (2^48) 2792882177 9 Manual.Count131072.C021278.packed 128 cuts21278 = true := by
 decide +kernel
def pointBounds21278 : List (Nat × Nat × Nat) := [(2792962048,100822697093804,100823077930533)]
theorem point_links_checked21278 : (cuts21278.take 1).map (fun c => (2792882177-1+2*2^9*c.k,100822325310804+c.lower,100822706147321+c.upper)) = pointBounds21278 := by
 decide +kernel
def cuts21279 : List PrefixCut := [⟨36,166484517,166484612⟩,
⟨122,575027626,575027948⟩,
⟨128,602941913,602942251⟩]
theorem checked21279 : checkPrefixCuts (2^48) 2793013249 9 Manual.Count131072.C021279.packed 128 cuts21279 = true := by
 decide +kernel
def pointBounds21279 : List (Nat × Nat × Nat) := [(2793050112,100823101215562,100823482052517),(2793138176,100823509758671,100823890595853)]
theorem point_links_checked21279 : (cuts21279.take 2).map (fun c => (2793013249-1+2*2^9*c.k,100822934731045+c.lower,100823315567905+c.upper)) = pointBounds21279 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S3.B000039
