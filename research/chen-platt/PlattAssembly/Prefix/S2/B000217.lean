import PlattAssemblyKernel
import PlattCertificates.Count131072.C016944
import PlattCertificates.Count131072.C016945
import PlattCertificates.Count131072.C016946
import PlattCertificates.Count131072.C016947
import PlattCertificates.Count131072.C016948
import PlattCertificates.Count131072.C016949
import PlattCertificates.Count131072.C016950
import PlattCertificates.Count131072.C016951
import PlattCertificates.Count131072.C016952
import PlattCertificates.Count131072.C016953
import PlattCertificates.Count131072.C016954
import PlattCertificates.Count131072.C016955
import PlattCertificates.Count131072.C016956
import PlattCertificates.Count131072.C016957
import PlattCertificates.Count131072.C016958
import PlattCertificates.Count131072.C016959
import PlattCertificates.Count131072.C016960
import PlattCertificates.Count131072.C016961
import PlattCertificates.Count131072.C016962
import PlattCertificates.Count131072.C016963
import PlattCertificates.Count131072.C016964
import PlattCertificates.Count131072.C016965
import PlattCertificates.Count131072.C016966
import PlattCertificates.Count131072.C016967
import PlattCertificates.Count131072.C016968
import PlattCertificates.Count131072.C016969
import PlattCertificates.Count131072.C016970
import PlattCertificates.Count131072.C016971
import PlattCertificates.Count131072.C016972
import PlattCertificates.Count131072.C016973
import PlattCertificates.Count131072.C016974
import PlattCertificates.Count131072.C016975
namespace ChenEffective.PlattWindow.Assembly.Prefix.S2.B000217
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts16944 : List PrefixCut := [⟨8,48455552,48455582⟩,
⟨76,456082256,456082541⟩,
⟨128,775773300,775773789⟩]
theorem checked16944 : checkPrefixCuts (2^48) 2224816129 9 Manual.Count131072.C016944.packed 128 cuts16944 = true := by
 decide +kernel
def pointBounds16944 : List (Nat × Nat × Nat) := [(2224824320,97864000865010,97864379928284),(2224893952,97864408491714,97864787555243)]
theorem point_links_checked16944 : (cuts16944.take 2).map (fun c => (2224816129-1+2*2^9*c.k,97863952409458+c.lower,97864331472702+c.upper)) = pointBounds16944 := by
 decide +kernel
def cuts16945 : List PrefixCut := [⟨16,95007587,95007649⟩,
⟨84,510705197,510705518⟩,
⟨128,774209690,774210172⟩]
theorem checked16945 : checkPrefixCuts (2^48) 2224947201 9 Manual.Count131072.C016945.packed 128 cuts16945 = true := by
 decide +kernel
def pointBounds16945 : List (Nat × Nat × Nat) := [(2224963584,97864823190345,97865202254140),(2225033216,97865238887955,97865617952009)]
theorem point_links_checked16945 : (cuts16945.take 2).map (fun c => (2224947201-1+2*2^9*c.k,97864728182758+c.lower,97865107246491+c.upper)) = pointBounds16945 := by
 decide +kernel
def cuts16946 : List PrefixCut := [⟨24,148511491,148511584⟩,
⟨92,565954048,565954407⟩,
⟨128,780868560,780869052⟩]
theorem checked16946 : checkPrefixCuts (2^48) 2225078273 9 Manual.Count131072.C016946.packed 128 cuts16946 = true := by
 decide +kernel
def pointBounds16946 : List (Nat × Nat × Nat) := [(2225102848,97865650903939,97866029968247),(2225172480,97866068346496,97866447411070)]
theorem point_links_checked16946 : (cuts16946.take 2).map (fun c => (2225078273-1+2*2^9*c.k,97865502392448+c.lower,97865881456663+c.upper)) = pointBounds16946 := by
 decide +kernel
def cuts16947 : List PrefixCut := [⟨32,189992110,189992231⟩,
⟨100,603487333,603487714⟩,
⟨128,769564807,769565294⟩]
theorem checked16947 : checkPrefixCuts (2^48) 2225209345 9 Manual.Count131072.C016947.packed 128 cuts16947 = true := by
 decide +kernel
def pointBounds16947 : List (Nat × Nat × Nat) := [(2225242112,97866473253118,97866852317946),(2225311744,97866886748341,97867265813429)]
theorem point_links_checked16947 : (cuts16947.take 2).map (fun c => (2225209345-1+2*2^9*c.k,97866283261008+c.lower,97866662325715+c.upper)) = pointBounds16947 := by
 decide +kernel
def cuts16948 : List PrefixCut := [⟨40,238297877,238298024⟩,
⟨108,654296951,654297358⟩,
⟨128,776349500,776349985⟩]
theorem checked16948 : checkPrefixCuts (2^48) 2225340417 9 Manual.Count131072.C016948.packed 128 cuts16948 = true := by
 decide +kernel
def pointBounds16948 : List (Nat × Nat × Nat) := [(2225381376,97867291123692,97867670189033),(2225451008,97867707122766,97868086188367)]
theorem point_links_checked16948 : (cuts16948.take 2).map (fun c => (2225340417-1+2*2^9*c.k,97867052825815+c.lower,97867431891009+c.upper)) = pointBounds16948 := by
 decide +kernel
def cuts16949 : List PrefixCut := [⟨48,283182859,283183041⟩,
⟨116,694729149,694729592⟩,
⟨128,765806228,765806714⟩]
theorem checked16949 : checkPrefixCuts (2^48) 2225471489 9 Manual.Count131072.C016949.packed 128 cuts16949 = true := by
 decide +kernel
def pointBounds16949 : List (Nat × Nat × Nat) := [(2225520640,97868112358174,97868491424035),(2225590272,97868523904464,97868902970586)]
theorem point_links_checked16949 : (cuts16949.take 2).map (fun c => (2225471489-1+2*2^9*c.k,97867829175315+c.lower,97868208240994+c.upper)) = pointBounds16949 := by
 decide +kernel
def cuts16950 : List PrefixCut := [⟨56,336409389,336409601⟩,
⟨124,738824476,738824940⟩,
⟨128,765002522,765003002⟩]
theorem checked16950 : checkPrefixCuts (2^48) 2225602561 9 Manual.Count131072.C016950.packed 128 cuts16950 = true := by
 decide +kernel
def pointBounds16950 : List (Nat × Nat × Nat) := [(2225659904,97868931390932,97869310457309),(2225729536,97869333806019,97869712872648)]
theorem point_links_checked16950 : (cuts16950.take 2).map (fun c => (2225602561-1+2*2^9*c.k,97868594981543+c.lower,97868974047708+c.upper)) = pointBounds16950 := by
 decide +kernel
def cuts16951 : List PrefixCut := [⟨64,375465753,375465988⟩,
⟨128,763945601,763946080⟩]
theorem checked16951 : checkPrefixCuts (2^48) 2225733633 9 Manual.Count131072.C016951.packed 128 cuts16951 = true := by
 decide +kernel
def pointBounds16951 : List (Nat × Nat × Nat) := [(2225799168,97869735449818,97870114516698)]
theorem point_links_checked16951 : (cuts16951.take 1).map (fun c => (2225733633-1+2*2^9*c.k,97869359984065+c.lower,97869739050710+c.upper)) = pointBounds16951 := by
 decide +kernel
def cuts16952 : List PrefixCut := [⟨4,23394415,23394432⟩,
⟨72,435888113,435888384⟩,
⟨128,776040256,776040738⟩]
theorem checked16952 : checkPrefixCuts (2^48) 2225864705 9 Manual.Count131072.C016952.packed 128 cuts16952 = true := by
 decide +kernel
def pointBounds16952 : List (Nat × Nat × Nat) := [(2225868800,97870147324081,97870526391222),(2225938432,97870559817779,97870938885174)]
theorem point_links_checked16952 : (cuts16952.take 2).map (fun c => (2225864705-1+2*2^9*c.k,97870123929666+c.lower,97870502996790+c.upper)) = pointBounds16952 := by
 decide +kernel
def cuts16953 : List PrefixCut := [⟨12,71696370,71696417⟩,
⟨80,473669151,473669451⟩,
⟨128,760821047,760821531⟩]
theorem checked16953 : checkPrefixCuts (2^48) 2225995777 9 Manual.Count131072.C016953.packed 128 cuts16953 = true := by
 decide +kernel
def pointBounds16953 : List (Nat × Nat × Nat) := [(2226008064,97870971666292,97871350733945),(2226077696,97871373639073,97871752706979)]
theorem point_links_checked16953 : (cuts16953.take 2).map (fun c => (2225995777-1+2*2^9*c.k,97870899969922+c.lower,97871279037528+c.upper)) = pointBounds16953 := by
 decide +kernel
def cuts16954 : List PrefixCut := [⟨20,120118901,120118977⟩,
⟨88,526491915,526492243⟩,
⟨128,768615437,768615916⟩]
theorem checked16954 : checkPrefixCuts (2^48) 2226126849 9 Manual.Count131072.C016954.packed 128 cuts16954 = true := by
 decide +kernel
def pointBounds16954 : List (Nat × Nat × Nat) := [(2226147328,97871780909870,97872159978036),(2226216960,97872187282884,97872566351302)]
theorem point_links_checked16954 : (cuts16954.take 2).map (fun c => (2226126849-1+2*2^9*c.k,97871660790969+c.lower,97872039859059+c.upper)) = pointBounds16954 := by
 decide +kernel
def cuts16955 : List PrefixCut := [⟨28,166512610,166512714⟩,
⟨96,576273811,576274174⟩,
⟨128,772362991,772363473⟩]
theorem checked16955 : checkPrefixCuts (2^48) 2226257921 9 Manual.Count131072.C016955.packed 128 cuts16955 = true := by
 decide +kernel
def pointBounds16955 : List (Nat × Nat × Nat) := [(2226286592,97872595919016,97872974987689),(2226356224,97873005680217,97873384749149)]
theorem point_links_checked16955 : (cuts16955.take 2).map (fun c => (2226257921-1+2*2^9*c.k,97872429406406+c.lower,97872808474975+c.upper)) = pointBounds16955 := by
 decide +kernel
def cuts16956 : List PrefixCut := [⟨36,215682074,215682210⟩,
⟨104,624911958,624912352⟩,
⟨128,771559036,771559524⟩]
theorem checked16956 : checkPrefixCuts (2^48) 2226388993 9 Manual.Count131072.C016956.packed 128 cuts16956 = true := by
 decide +kernel
def pointBounds16956 : List (Nat × Nat × Nat) := [(2226425856,97873417451471,97873796520658),(2226495488,97873826681355,97874205750800)]
theorem point_links_checked16956 : (cuts16956.take 2).map (fun c => (2226388993-1+2*2^9*c.k,97873201769397+c.lower,97873580838448+c.upper)) = pointBounds16956 := by
 decide +kernel
def cuts16957 : List PrefixCut := [⟨44,260800168,260800334⟩,
⟨112,676578072,676578500⟩,
⟨128,770628767,770629257⟩]
theorem checked16957 : checkPrefixCuts (2^48) 2226520065 9 Manual.Count131072.C016957.packed 128 cuts16957 = true := by
 decide +kernel
def pointBounds16957 : List (Nat × Nat × Nat) := [(2226565120,97874234128601,97874613198306),(2226634752,97874649906505,97875028976472)]
theorem point_links_checked16957 : (cuts16957.take 2).map (fun c => (2226520065-1+2*2^9*c.k,97873973328433+c.lower,97874352397972+c.upper)) = pointBounds16957 := by
 decide +kernel
def cuts16958 : List PrefixCut := [⟨52,315646371,315646565⟩,
⟨120,729754877,729755335⟩,
⟨128,778926250,778926739⟩]
theorem checked16958 : checkPrefixCuts (2^48) 2226651137 9 Manual.Count131072.C016958.packed 128 cuts16958 = true := by
 decide +kernel
def pointBounds16958 : List (Nat × Nat × Nat) := [(2226704384,97875059603571,97875438673794),(2226774016,97875473712077,97875852782564)]
theorem point_links_checked16958 : (cuts16958.take 2).map (fun c => (2226651137-1+2*2^9*c.k,97874743957200+c.lower,97875123027229+c.upper)) = pointBounds16958 := by
 decide +kernel
def cuts16959 : List PrefixCut := [⟨60,356708050,356708270⟩,
⟨128,769653069,769653549⟩]
theorem checked16959 : checkPrefixCuts (2^48) 2226782209 9 Manual.Count131072.C016959.packed 128 cuts16959 = true := by
 decide +kernel
def pointBounds16959 : List (Nat × Nat × Nat) := [(2226843648,97875879591500,97876258662238),(2226913280,97876292536519,97876671607517)]
theorem point_links_checked16959 : (cuts16959.take 2).map (fun c => (2226782209-1+2*2^9*c.k,97875522883450+c.lower,97875901953968+c.upper)) = pointBounds16959 := by
 decide +kernel
def cuts16960 : List PrefixCut := [⟨68,412932197,412932460⟩,
⟨128,770492866,770493352⟩]
theorem checked16960 : checkPrefixCuts (2^48) 2226913281 9 Manual.Count131072.C016960.packed 128 cuts16960 = true := by
 decide +kernel
def pointBounds16960 : List (Nat × Nat × Nat) := [(2226982912,97876705468716,97877084539977)]
theorem point_links_checked16960 : (cuts16960.take 1).map (fun c => (2226913281-1+2*2^9*c.k,97876292536519+c.lower,97876671607517+c.upper)) = pointBounds16960 := by
 decide +kernel
def cuts16961 : List PrefixCut := [⟨8,50050124,50050154⟩,
⟨76,450823321,450823603⟩,
⟨128,759704596,759705073⟩]
theorem checked16961 : checkPrefixCuts (2^48) 2227044353 9 Manual.Count131072.C016961.packed 128 cuts16961 = true := by
 decide +kernel
def pointBounds16961 : List (Nat × Nat × Nat) := [(2227052544,97877113079509,97877492151023),(2227122176,97877513852706,97877892924472)]
theorem point_links_checked16961 : (cuts16961.take 2).map (fun c => (2227044353-1+2*2^9*c.k,97877063029385+c.lower,97877442100869+c.upper)) = pointBounds16961 := by
 decide +kernel
def cuts16962 : List PrefixCut := [⟨16,95670828,95670886⟩,
⟨84,497809108,497809411⟩,
⟨128,770022709,770023178⟩]
theorem checked16962 : checkPrefixCuts (2^48) 2227175425 9 Manual.Count131072.C016962.packed 128 cuts16962 = true := by
 decide +kernel
def pointBounds16962 : List (Nat × Nat × Nat) := [(2227191808,97877918404809,97878297476828),(2227261440,97878320543089,97878699615353)]
theorem point_links_checked16962 : (cuts16962.take 2).map (fun c => (2227175425-1+2*2^9*c.k,97877822733981+c.lower,97878201805942+c.upper)) = pointBounds16962 := by
 decide +kernel
def cuts16963 : List PrefixCut := [⟨24,142549715,142549798⟩,
⟨92,548074809,548075146⟩,
⟨128,766186248,766186718⟩]
theorem checked16963 : checkPrefixCuts (2^48) 2227306497 9 Manual.Count131072.C016963.packed 128 cuts16963 = true := by
 decide +kernel
def pointBounds16963 : List (Nat × Nat × Nat) := [(2227331072,97878735306405,97879114378918),(2227400704,97879140831499,97879519904266)]
theorem point_links_checked16963 : (cuts16963.take 2).map (fun c => (2227306497-1+2*2^9*c.k,97878592756690+c.lower,97878971829120+c.upper)) = pointBounds16963 := by
 decide +kernel
def cuts16964 : List PrefixCut := [⟨32,195235775,195235896⟩,
⟨100,611097352,611097735⟩,
⟨128,781684020,781684512⟩]
theorem checked16964 : checkPrefixCuts (2^48) 2227437569 9 Manual.Count131072.C016964.packed 128 cuts16964 = true := by
 decide +kernel
def pointBounds16964 : List (Nat × Nat × Nat) := [(2227470336,97879554178713,97879933251734),(2227539968,97879970040290,97880349113573)]
theorem point_links_checked16964 : (cuts16964.take 2).map (fun c => (2227437569-1+2*2^9*c.k,97879358942938+c.lower,97879738015838+c.upper)) = pointBounds16964 := by
 decide +kernel
def cuts16965 : List PrefixCut := [⟨40,236795868,236796016⟩,
⟨108,641891216,641891624⟩,
⟨128,766475108,766475594⟩]
theorem checked16965 : checkPrefixCuts (2^48) 2227568641 9 Manual.Count131072.C016965.packed 128 cuts16965 = true := by
 decide +kernel
def pointBounds16965 : List (Nat × Nat × Nat) := [(2227609600,97880377422826,97880756496366),(2227679232,97880782518174,97881161591974)]
theorem point_links_checked16965 : (cuts16965.take 2).map (fun c => (2227568641-1+2*2^9*c.k,97880140626958+c.lower,97880519700350+c.upper)) = pointBounds16965 := by
 decide +kernel
def cuts16966 : List PrefixCut := [⟨48,295408355,295408537⟩,
⟨116,702626290,702626724⟩,
⟨128,775148417,775148899⟩]
theorem checked16966 : checkPrefixCuts (2^48) 2227699713 9 Manual.Count131072.C016966.packed 128 cuts16966 = true := by
 decide +kernel
def pointBounds16966 : List (Nat × Nat × Nat) := [(2227748864,97881202510421,97881581584481),(2227818496,97881609728356,97881988802668)]
theorem point_links_checked16966 : (cuts16966.take 2).map (fun c => (2227699713-1+2*2^9*c.k,97880907102066+c.lower,97881286175944+c.upper)) = pointBounds16966 := by
 decide +kernel
def cuts16967 : List PrefixCut := [⟨56,332535212,332535418⟩,
⟨124,745918321,745918785⟩,
⟨128,769417098,769417577⟩]
theorem checked16967 : checkPrefixCuts (2^48) 2227830785 9 Manual.Count131072.C016967.packed 128 cuts16967 = true := by
 decide +kernel
def pointBounds16967 : List (Nat × Nat × Nat) := [(2227888128,97882014785695,97882393860261),(2227957760,97882428168804,97882807243628)]
theorem point_links_checked16967 : (cuts16967.take 2).map (fun c => (2227830785-1+2*2^9*c.k,97881682250483+c.lower,97882061324843+c.upper)) = pointBounds16967 := by
 decide +kernel
def cuts16968 : List PrefixCut := [⟨64,386081385,386081622⟩,
⟨128,764950513,764950986⟩]
theorem checked16968 : checkPrefixCuts (2^48) 2227961857 9 Manual.Count131072.C016968.packed 128 cuts16968 = true := by
 decide +kernel
def pointBounds16968 : List (Nat × Nat × Nat) := [(2228027392,97882837748966,97883216824042)]
theorem point_links_checked16968 : (cuts16968.take 1).map (fun c => (2227961857-1+2*2^9*c.k,97882451667581+c.lower,97882830742420+c.upper)) = pointBounds16968 := by
 decide +kernel
def cuts16969 : List PrefixCut := [⟨4,23623680,23623695⟩,
⟨72,433809940,433810209⟩,
⟨128,764273891,764274371⟩]
theorem checked16969 : checkPrefixCuts (2^48) 2228092929 9 Manual.Count131072.C016969.packed 128 cuts16969 = true := by
 decide +kernel
def pointBounds16969 : List (Nat × Nat × Nat) := [(2228097024,97883240241774,97883619317101),(2228166656,97883650428034,97884029503615)]
theorem point_links_checked16969 : (cuts16969.take 2).map (fun c => (2228092929-1+2*2^9*c.k,97883216618094+c.lower,97883595693406+c.upper)) = pointBounds16969 := by
 decide +kernel
def cuts16970 : List PrefixCut := [⟨12,71498362,71498405⟩,
⟨80,481406299,481406593⟩,
⟨128,776607935,776608417⟩]
theorem checked16970 : checkPrefixCuts (2^48) 2228224001 9 Manual.Count131072.C016970.packed 128 cuts16970 = true := by
 decide +kernel
def pointBounds16970 : List (Nat × Nat × Nat) := [(2228236288,97884052390347,97884431466182),(2228305920,97884462298284,97884841374370)]
theorem point_links_checked16970 : (cuts16970.take 2).map (fun c => (2228224001-1+2*2^9*c.k,97883980891985+c.lower,97884359967777+c.upper)) = pointBounds16970 := by
 decide +kernel
def cuts16971 : List PrefixCut := [⟨21,127198679,127198757⟩,
⟨90,542259455,542259791⟩,
⟨128,769615248,769615727⟩]
theorem checked16971 : checkPrefixCuts (2^48) 2228355073 9 Manual.Count131072.C016971.packed 128 cuts16971 = true := by
 decide +kernel
def pointBounds16971 : List (Nat × Nat × Nat) := [(2228376576,97884884698599,97885263774951),(2228447232,97885299759375,97885678835985)]
theorem point_links_checked16971 : (cuts16971.take 2).map (fun c => (2228355073-1+2*2^9*c.k,97884757499920+c.lower,97885136576194+c.upper)) = pointBounds16971 := by
 decide +kernel
def cuts16972 : List PrefixCut := [⟨31,186049865,186049981⟩,
⟨100,596790059,596790429⟩,
⟨128,764012631,764013107⟩]
theorem checked16972 : checkPrefixCuts (2^48) 2228486145 9 Manual.Count131072.C016972.packed 128 cuts16972 = true := by
 decide +kernel
def pointBounds16972 : List (Nat × Nat × Nat) := [(2228517888,97885713165033,97886092241902),(2228588544,97886123905227,97886502982350)]
theorem point_links_checked16972 : (cuts16972.take 2).map (fun c => (2228486145-1+2*2^9*c.k,97885527115168+c.lower,97885906191921+c.upper)) = pointBounds16972 := by
 decide +kernel
def cuts16973 : List PrefixCut := [⟨41,247546144,247546300⟩,
⟨110,656744744,656745156⟩,
⟨128,765862187,765862665⟩]
theorem checked16973 : checkPrefixCuts (2^48) 2228617217 9 Manual.Count131072.C016973.packed 128 cuts16973 = true := by
 decide +kernel
def pointBounds16973 : List (Nat × Nat × Nat) := [(2228659200,97886538673943,97886917751328),(2228729856,97886947872543,97887326950184)]
theorem point_links_checked16973 : (cuts16973.take 2).map (fun c => (2228617217-1+2*2^9*c.k,97886291127799+c.lower,97886670205028+c.upper)) = pointBounds16973 := by
 decide +kernel
def cuts16974 : List PrefixCut := [⟨51,306130250,306130441⟩,
⟨120,724900803,724901254⟩,
⟨128,776425334,776425818⟩]
theorem checked16974 : checkPrefixCuts (2^48) 2228748289 9 Manual.Count131072.C016974.packed 128 cuts16974 = true := by
 decide +kernel
def pointBounds16974 : List (Nat × Nat × Nat) := [(2228800512,97887363120236,97887742198134),(2228871168,97887781890789,97888160968947)]
theorem point_links_checked16974 : (cuts16974.take 2).map (fun c => (2228748289-1+2*2^9*c.k,97887056989986+c.lower,97887436067693+c.upper)) = pointBounds16974 := by
 decide +kernel
def cuts16975 : List PrefixCut := [⟨61,362560307,362560536⟩,
⟨128,761478591,761479071⟩]
theorem checked16975 : checkPrefixCuts (2^48) 2228879361 9 Manual.Count131072.C016975.packed 128 cuts16975 = true := by
 decide +kernel
def pointBounds16975 : List (Nat × Nat × Nat) := [(2228941824,97888195975627,97888575054047)]
theorem point_links_checked16975 : (cuts16975.take 1).map (fun c => (2228879361-1+2*2^9*c.k,97887833415320+c.lower,97888212493511+c.upper)) = pointBounds16975 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S2.B000217
