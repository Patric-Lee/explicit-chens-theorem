import PlattAssemblyKernel
import PlattCertificates.Count131072.C018512
import PlattCertificates.Count131072.C018513
import PlattCertificates.Count131072.C018514
import PlattCertificates.Count131072.C018515
import PlattCertificates.Count131072.C018516
import PlattCertificates.Count131072.C018517
import PlattCertificates.Count131072.C018518
import PlattCertificates.Count131072.C018519
import PlattCertificates.Count131072.C018520
import PlattCertificates.Count131072.C018521
import PlattCertificates.Count131072.C018522
import PlattCertificates.Count131072.C018523
import PlattCertificates.Count131072.C018524
import PlattCertificates.Count131072.C018525
import PlattCertificates.Count131072.C018526
import PlattCertificates.Count131072.C018527
import PlattCertificates.Count131072.C018528
import PlattCertificates.Count131072.C018529
import PlattCertificates.Count131072.C018530
import PlattCertificates.Count131072.C018531
import PlattCertificates.Count131072.C018532
import PlattCertificates.Count131072.C018533
import PlattCertificates.Count131072.C018534
import PlattCertificates.Count131072.C018535
import PlattCertificates.Count131072.C018536
import PlattCertificates.Count131072.C018537
import PlattCertificates.Count131072.C018538
import PlattCertificates.Count131072.C018539
import PlattCertificates.Count131072.C018540
import PlattCertificates.Count131072.C018541
import PlattCertificates.Count131072.C018542
import PlattCertificates.Count131072.C018543
namespace ChenEffective.PlattWindow.Assembly.Prefix.S2.B000266
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts18512 : List PrefixCut := [⟨41,224567649,224567785⟩,
⟨116,636168428,636168811⟩,
⟨128,702528282,702528704⟩]
theorem checked18512 : checkPrefixCuts (2^48) 2430337025 9 Manual.Count131072.C018512.packed 128 cuts18512 = true := by
 decide +kernel
def pointBounds18512 : List (Nat × Nat × Nat) := [(2430379008,99017378011609,99017757783716),(2430455808,99017789612388,99018169384742)]
theorem point_links_checked18512 : (cuts18512.take 2).map (fun c => (2430337025-1+2*2^9*c.k,99017153443960+c.lower,99017533215931+c.upper)) = pointBounds18512 := by
 decide +kernel
def cuts18513 : List PrefixCut := [⟨63,349397119,349397324⟩,
⟨128,711407724,711408146⟩]
theorem checked18513 : checkPrefixCuts (2^48) 2430468097 9 Manual.Count131072.C018513.packed 128 cuts18513 = true := by
 decide +kernel
def pointBounds18513 : List (Nat × Nat × Nat) := [(2430532608,99018205369361,99018585141959)]
theorem point_links_checked18513 : (cuts18513.take 1).map (fun c => (2430468097-1+2*2^9*c.k,99017855972242+c.lower,99018235744635+c.upper)) = pointBounds18513 := by
 decide +kernel
def cuts18514 : List PrefixCut := [⟨10,54428112,54428143⟩,
⟨85,464252842,464253118⟩,
⟨128,696894118,696894540⟩]
theorem checked18514 : checkPrefixCuts (2^48) 2430599169 9 Manual.Count131072.C018514.packed 128 cuts18514 = true := by
 decide +kernel
def pointBounds18514 : List (Nat × Nat × Nat) := [(2430609408,99018621808078,99019001580924),(2430686208,99019031632808,99019411405899)]
theorem point_links_checked18514 : (cuts18514.take 2).map (fun c => (2430599169-1+2*2^9*c.k,99018567379966+c.lower,99018947152781+c.upper)) = pointBounds18514 := by
 decide +kernel
def cuts18515 : List PrefixCut := [⟨32,175086136,175086242⟩,
⟨107,592064274,592064626⟩,
⟨128,708899177,708899601⟩]
theorem checked18515 : checkPrefixCuts (2^48) 2430730241 9 Manual.Count131072.C018515.packed 128 cuts18515 = true := by
 decide +kernel
def pointBounds18515 : List (Nat × Nat × Nat) := [(2430763008,99019439360220,99019819133563),(2430839808,99019856338358,99020236111947)]
theorem point_links_checked18515 : (cuts18515.take 2).map (fun c => (2430730241-1+2*2^9*c.k,99019264274084+c.lower,99019644047321+c.upper)) = pointBounds18515 := by
 decide +kernel
def cuts18516 : List PrefixCut := [⟨54,293182620,293182799⟩,
⟨128,695776795,695777226⟩]
theorem checked18516 : checkPrefixCuts (2^48) 2430861313 9 Manual.Count131072.C018516.packed 128 cuts18516 = true := by
 decide +kernel
def pointBounds18516 : List (Nat × Nat × Nat) := [(2430916608,99020266355881,99020646129721)]
theorem point_links_checked18516 : (cuts18516.take 1).map (fun c => (2430861313-1+2*2^9*c.k,99019973173261+c.lower,99020352946922+c.upper)) = pointBounds18516 := by
 decide +kernel
def cuts18517 : List PrefixCut := [⟨1,5210369,5210372⟩,
⟨76,413117919,413118169⟩,
⟨128,698402371,698402787⟩]
theorem checked18517 : checkPrefixCuts (2^48) 2430992385 9 Manual.Count131072.C018517.packed 128 cuts18517 = true := by
 decide +kernel
def pointBounds18517 : List (Nat × Nat × Nat) := [(2430993408,99020674160425,99021053934520),(2431070208,99021082067975,99021461842317)]
theorem point_links_checked18517 : (cuts18517.take 2).map (fun c => (2430992385-1+2*2^9*c.k,99020668950056+c.lower,99021048724148+c.upper)) = pointBounds18517 := by
 decide +kernel
def cuts18518 : List PrefixCut := [⟨23,125273092,125273168⟩,
⟨98,532923222,532923546⟩,
⟨128,700332773,700333198⟩]
theorem checked18518 : checkPrefixCuts (2^48) 2431123457 9 Manual.Count131072.C018518.packed 128 cuts18518 = true := by
 decide +kernel
def pointBounds18518 : List (Nat × Nat × Nat) := [(2431147008,99021492625519,99021872400103),(2431223808,99021900275649,99022280050481)]
theorem point_links_checked18518 : (cuts18518.take 2).map (fun c => (2431123457-1+2*2^9*c.k,99021367352427+c.lower,99021747126935+c.upper)) = pointBounds18518 := by
 decide +kernel
def cuts18519 : List PrefixCut := [⟨45,247058333,247058486⟩,
⟨120,655956221,655956622⟩,
⟨128,698558647,698559074⟩]
theorem checked18519 : checkPrefixCuts (2^48) 2431254529 9 Manual.Count131072.C018519.packed 128 cuts18519 = true := by
 decide +kernel
def pointBounds18519 : List (Nat × Nat × Nat) := [(2431300608,99022314743533,99022694518619),(2431377408,99022723641421,99023103416755)]
theorem point_links_checked18519 : (cuts18519.take 2).map (fun c => (2431254529-1+2*2^9*c.k,99022067685200+c.lower,99022447460133+c.upper)) = pointBounds18519 := by
 decide +kernel
def cuts18520 : List PrefixCut := [⟨67,371491938,371492156⟩,
⟨128,712644068,712644491⟩]
theorem checked18520 : checkPrefixCuts (2^48) 2431385601 9 Manual.Count131072.C018520.packed 128 cuts18520 = true := by
 decide +kernel
def pointBounds18520 : List (Nat × Nat × Nat) := [(2431454208,99023137735785,99023517511363)]
theorem point_links_checked18520 : (cuts18520.take 1).map (fun c => (2431385601-1+2*2^9*c.k,99022766243847+c.lower,99023146019207+c.upper)) = pointBounds18520 := by
 decide +kernel
def cuts18521 : List PrefixCut := [⟨14,74434126,74434173⟩,
⟨89,481441105,481441398⟩,
⟨128,696283788,696284211⟩]
theorem checked18521 : checkPrefixCuts (2^48) 2431516673 9 Manual.Count131072.C018521.packed 128 cuts18521 = true := by
 decide +kernel
def pointBounds18521 : List (Nat × Nat × Nat) := [(2431531008,99023553322041,99023933097871),(2431607808,99023960329020,99024340105096)]
theorem point_links_checked18521 : (cuts18521.take 2).map (fun c => (2431516673-1+2*2^9*c.k,99023478887915+c.lower,99023858663698+c.upper)) = pointBounds18521 := by
 decide +kernel
def cuts18522 : List PrefixCut := [⟨36,197013200,197013314⟩,
⟨111,608740228,608740590⟩,
⟨128,700181915,700182332⟩]
theorem checked18522 : checkPrefixCuts (2^48) 2431647745 9 Manual.Count131072.C018522.packed 128 cuts18522 = true := by
 decide +kernel
def pointBounds18522 : List (Nat × Nat × Nat) := [(2431684608,99024372184903,99024751961223),(2431761408,99024783911931,99025163688499)]
theorem point_links_checked18522 : (cuts18522.take 2).map (fun c => (2431647745-1+2*2^9*c.k,99024175171703+c.lower,99024554947909+c.upper)) = pointBounds18522 := by
 decide +kernel
def cuts18523 : List PrefixCut := [⟨58,318188900,318189094⟩,
⟨128,692505079,692505500⟩]
theorem checked18523 : checkPrefixCuts (2^48) 2431778817 9 Manual.Count131072.C018523.packed 128 cuts18523 = true := by
 decide +kernel
def pointBounds18523 : List (Nat × Nat × Nat) := [(2431838208,99025193542518,99025573319335)]
theorem point_links_checked18523 : (cuts18523.take 1).map (fun c => (2431778817-1+2*2^9*c.k,99024875353618+c.lower,99025255130241+c.upper)) = pointBounds18523 := by
 decide +kernel
def cuts18524 : List PrefixCut := [⟨5,29167036,29167052⟩,
⟨80,446063424,446063697⟩,
⟨128,709134221,709134659⟩]
theorem checked18524 : checkPrefixCuts (2^48) 2431909889 9 Manual.Count131072.C018524.packed 128 cuts18524 = true := by
 decide +kernel
def pointBounds18524 : List (Nat × Nat × Nat) := [(2431915008,99025597025733,99025976802793),(2431991808,99026013922121,99026393699438)]
theorem point_links_checked18524 : (cuts18524.take 2).map (fun c => (2431909889-1+2*2^9*c.k,99025567858697+c.lower,99025947635741+c.upper)) = pointBounds18524 := by
 decide +kernel
def cuts18525 : List PrefixCut := [⟨27,140850008,140850093⟩,
⟨102,554942482,554942811⟩,
⟨128,695786476,695786890⟩]
theorem checked18525 : checkPrefixCuts (2^48) 2432040961 9 Manual.Count131072.C018525.packed 128 cuts18525 = true := by
 decide +kernel
def pointBounds18525 : List (Nat × Nat × Nat) := [(2432068608,99026417842926,99026797620493),(2432145408,99026831935400,99027211713211)]
theorem point_links_checked18525 : (cuts18525.take 2).map (fun c => (2432040961-1+2*2^9*c.k,99026276992918+c.lower,99026656770400+c.upper)) = pointBounds18525 := by
 decide +kernel
def cuts18526 : List PrefixCut := [⟨49,268027574,268027736⟩,
⟨124,685797187,685797600⟩,
⟨128,709173376,709173803⟩]
theorem checked18526 : checkPrefixCuts (2^48) 2432172033 9 Manual.Count131072.C018526.packed 128 cuts18526 = true := by
 decide +kernel
def pointBounds18526 : List (Nat × Nat × Nat) := [(2432222208,99027240806968,99027620585026),(2432299008,99027658576581,99028038354890)]
theorem point_links_checked18526 : (cuts18526.take 2).map (fun c => (2432172033-1+2*2^9*c.k,99026972779394+c.lower,99027352557290+c.upper)) = pointBounds18526 := by
 decide +kernel
def cuts18527 : List PrefixCut := [⟨71,395768826,395769065⟩,
⟨128,703233489,703233915⟩]
theorem checked18527 : checkPrefixCuts (2^48) 2432303105 9 Manual.Count131072.C018527.packed 128 cuts18527 = true := by
 decide +kernel
def pointBounds18527 : List (Nat × Nat × Nat) := [(2432375808,99028077721596,99028457500158)]
theorem point_links_checked18527 : (cuts18527.take 1).map (fun c => (2432303105-1+2*2^9*c.k,99027681952770+c.lower,99028061731093+c.upper)) = pointBounds18527 := by
 decide +kernel
def cuts18528 : List PrefixCut := [⟨18,101136596,101136657⟩,
⟨93,504633680,504633989⟩,
⟨128,698451266,698451696⟩]
theorem checked18528 : checkPrefixCuts (2^48) 2432434177 9 Manual.Count131072.C018528.packed 128 cuts18528 = true := by
 decide +kernel
def pointBounds18528 : List (Nat × Nat × Nat) := [(2432452608,99028486322855,99028866101665),(2432529408,99028889819939,99029269598997)]
theorem point_links_checked18528 : (cuts18528.take 2).map (fun c => (2432434177-1+2*2^9*c.k,99028385186259+c.lower,99028764965008+c.upper)) = pointBounds18528 := by
 decide +kernel
def cuts18529 : List PrefixCut := [⟨40,221816387,221816526⟩,
⟨115,637321469,637321859⟩,
⟨128,706976017,706976449⟩]
theorem checked18529 : checkPrefixCuts (2^48) 2432565249 9 Manual.Count131072.C018529.packed 128 cuts18529 = true := by
 decide +kernel
def pointBounds18529 : List (Nat × Nat × Nat) := [(2432606208,99029305453912,99029685233230),(2432683008,99029720958994,99030100738563)]
theorem point_links_checked18529 : (cuts18529.take 2).map (fun c => (2432565249-1+2*2^9*c.k,99029083637525+c.lower,99029463416704+c.upper)) = pointBounds18529 := by
 decide +kernel
def cuts18530 : List PrefixCut := [⟨62,342597756,342597958⟩,
⟨128,697681861,697682279⟩]
theorem checked18530 : checkPrefixCuts (2^48) 2432696321 9 Manual.Count131072.C018530.packed 128 cuts18530 = true := by
 decide +kernel
def pointBounds18530 : List (Nat × Nat × Nat) := [(2432759808,99030133211298,99030512991111)]
theorem point_links_checked18530 : (cuts18530.take 1).map (fun c => (2432696321-1+2*2^9*c.k,99029790613542+c.lower,99030170393153+c.upper)) = pointBounds18530 := by
 decide +kernel
def cuts18531 : List PrefixCut := [⟨9,52527095,52527128⟩,
⟨84,459084291,459084567⟩,
⟨128,703660353,703660777⟩]
theorem checked18531 : checkPrefixCuts (2^48) 2432827393 9 Manual.Count131072.C018531.packed 128 cuts18531 = true := by
 decide +kernel
def pointBounds18531 : List (Nat × Nat × Nat) := [(2432836608,99030540822498,99030920602560),(2432913408,99030947379694,99031327159999)]
theorem point_links_checked18531 : (cuts18531.take 2).map (fun c => (2432827393-1+2*2^9*c.k,99030488295403+c.lower,99030868075432+c.upper)) = pointBounds18531 := by
 decide +kernel
def cuts18532 : List PrefixCut := [⟨31,172611998,172612099⟩,
⟨106,585043584,585043936⟩,
⟨128,704316615,704317040⟩]
theorem checked18532 : checkPrefixCuts (2^48) 2432958465 9 Manual.Count131072.C018532.packed 128 cuts18532 = true := by
 decide +kernel
def pointBounds18532 : List (Nat × Nat × Nat) := [(2432990208,99031364567754,99031744348308),(2433067008,99031776999340,99032156780145)]
theorem point_links_checked18532 : (cuts18532.take 2).map (fun c => (2432958465-1+2*2^9*c.k,99031191955756+c.lower,99031571736209+c.upper)) = pointBounds18532 := by
 decide +kernel
def cuts18533 : List PrefixCut := [⟨53,290369148,290369326⟩,
⟨128,704510029,704510453⟩]
theorem checked18533 : checkPrefixCuts (2^48) 2433089537 9 Manual.Count131072.C018533.packed 128 cuts18533 = true := by
 decide +kernel
def pointBounds18533 : List (Nat × Nat × Nat) := [(2433143808,99032186641519,99032566422575),(2433220608,99032600782400,99032980563702)]
theorem point_links_checked18533 : (cuts18533.take 2).map (fun c => (2433089537-1+2*2^9*c.k,99031896272371+c.lower,99032276053249+c.upper)) = pointBounds18533 := by
 decide +kernel
def cuts18534 : List PrefixCut := [⟨75,415284482,415284738⟩,
⟨128,705628841,705629273⟩]
theorem checked18534 : checkPrefixCuts (2^48) 2433220609 9 Manual.Count131072.C018534.packed 128 cuts18534 = true := by
 decide +kernel
def pointBounds18534 : List (Nat × Nat × Nat) := [(2433297408,99033016066882,99033395848440)]
theorem point_links_checked18534 : (cuts18534.take 1).map (fun c => (2433220609-1+2*2^9*c.k,99032600782400+c.lower,99032980563702+c.upper)) = pointBounds18534 := by
 decide +kernel
def cuts18535 : List PrefixCut := [⟨22,117176945,117177018⟩,
⟨97,527230026,527230344⟩,
⟨128,693329673,693330092⟩]
theorem checked18535 : checkPrefixCuts (2^48) 2433351681 9 Manual.Count131072.C018535.packed 128 cuts18535 = true := by
 decide +kernel
def pointBounds18535 : List (Nat × Nat × Nat) := [(2433374208,99033423588186,99033803369993),(2433451008,99033833641267,99034213423319)]
theorem point_links_checked18535 : (cuts18535.take 2).map (fun c => (2433351681-1+2*2^9*c.k,99033306411241+c.lower,99033686192975+c.upper)) = pointBounds18535 := by
 decide +kernel
def cuts18536 : List PrefixCut := [⟨44,240701877,240702025⟩,
⟨119,657553306,657553705⟩,
⟨128,704627538,704627965⟩]
theorem checked18536 : checkPrefixCuts (2^48) 2433482753 9 Manual.Count131072.C018536.packed 128 cuts18536 = true := by
 decide +kernel
def pointBounds18536 : List (Nat × Nat × Nat) := [(2433527808,99034240442791,99034620225092),(2433604608,99034657294220,99035037076772)]
theorem point_links_checked18536 : (cuts18536.take 2).map (fun c => (2433482753-1+2*2^9*c.k,99033999740914+c.lower,99034379523067+c.upper)) = pointBounds18536 := by
 decide +kernel
def cuts18537 : List PrefixCut := [⟨66,353109005,353109224⟩,
⟨128,692445336,692445757⟩]
theorem checked18537 : checkPrefixCuts (2^48) 2433613825 9 Manual.Count131072.C018537.packed 128 cuts18537 = true := by
 decide +kernel
def pointBounds18537 : List (Nat × Nat × Nat) := [(2433681408,99035057477457,99035437260256)]
theorem point_links_checked18537 : (cuts18537.take 1).map (fun c => (2433613825-1+2*2^9*c.k,99034704368452+c.lower,99035084151032+c.upper)) = pointBounds18537 := by
 decide +kernel
def cuts18538 : List PrefixCut := [⟨13,70665039,70665082⟩,
⟨88,481000446,481000738⟩,
⟨128,703626313,703626737⟩]
theorem checked18538 : checkPrefixCuts (2^48) 2433744897 9 Manual.Count131072.C018538.packed 128 cuts18538 = true := by
 decide +kernel
def pointBounds18538 : List (Nat × Nat × Nat) := [(2433758208,99035467478827,99035847261871),(2433835008,99035877814234,99036257597527)]
theorem point_links_checked18538 : (cuts18538.take 2).map (fun c => (2433744897-1+2*2^9*c.k,99035396813788+c.lower,99035776596789+c.upper)) = pointBounds18538 := by
 decide +kernel
def cuts18539 : List PrefixCut := [⟨35,196254605,196254726⟩,
⟨110,609570889,609571259⟩,
⟨128,707289247,707289679⟩]
theorem checked18539 : checkPrefixCuts (2^48) 2433875969 9 Manual.Count131072.C018539.packed 128 cuts18539 = true := by
 decide +kernel
def pointBounds18539 : List (Nat × Nat × Nat) := [(2433911808,99036296694706,99036676478252),(2433988608,99036710010990,99037089794785)]
theorem point_links_checked18539 : (cuts18539.take 2).map (fun c => (2433875969-1+2*2^9*c.k,99036100440101+c.lower,99036480223526+c.upper)) = pointBounds18539 := by
 decide +kernel
def cuts18540 : List PrefixCut := [⟨57,306796135,306796323⟩,
⟨128,697652865,697653290⟩]
theorem checked18540 : checkPrefixCuts (2^48) 2434007041 9 Manual.Count131072.C018540.packed 128 cuts18540 = true := by
 decide +kernel
def pointBounds18540 : List (Nat × Nat × Nat) := [(2434065408,99037114525483,99037494309528)]
theorem point_links_checked18540 : (cuts18540.take 1).map (fun c => (2434007041-1+2*2^9*c.k,99036807729348+c.lower,99037187513205+c.upper)) = pointBounds18540 := by
 decide +kernel
def cuts18541 : List PrefixCut := [⟨4,22433436,22433449⟩,
⟨79,433744858,433745119⟩,
⟨128,703050246,703050669⟩]
theorem checked18541 : checkPrefixCuts (2^48) 2434138113 9 Manual.Count131072.C018541.packed 128 cuts18541 = true := by
 decide +kernel
def pointBounds18541 : List (Nat × Nat × Nat) := [(2434142208,99037527815649,99037907599944),(2434219008,99037939127071,99038318911614)]
theorem point_links_checked18541 : (cuts18541.take 2).map (fun c => (2434138113-1+2*2^9*c.k,99037505382213+c.lower,99037885166495+c.upper)) = pointBounds18541 := by
 decide +kernel
def cuts18542 : List PrefixCut := [⟨26,145346293,145346382⟩,
⟨101,560794314,560794653⟩,
⟨128,707868788,707869212⟩]
theorem checked18542 : checkPrefixCuts (2^48) 2434269185 9 Manual.Count131072.C018542.packed 128 cuts18542 = true := by
 decide +kernel
def pointBounds18542 : List (Nat × Nat × Nat) := [(2434295808,99038353778752,99038733563546),(2434372608,99038769226773,99039149011817)]
theorem point_links_checked18542 : (cuts18542.take 2).map (fun c => (2434269185-1+2*2^9*c.k,99038208432459+c.lower,99038588217164+c.upper)) = pointBounds18542 := by
 decide +kernel
def cuts18543 : List PrefixCut := [⟨48,255873170,255873325⟩,
⟨123,657073720,657074116⟩,
⟨128,683087727,683088139⟩]
theorem checked18543 : checkPrefixCuts (2^48) 2434400257 9 Manual.Count131072.C018543.packed 128 cuts18543 = true := by
 decide +kernel
def pointBounds18543 : List (Nat × Nat × Nat) := [(2434449408,99039172174417,99039551959701),(2434526208,99039573374967,99039953160492)]
theorem point_links_checked18543 : (cuts18543.take 2).map (fun c => (2434400257-1+2*2^9*c.k,99038916301247+c.lower,99039296086376+c.upper)) = pointBounds18543 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S2.B000266
