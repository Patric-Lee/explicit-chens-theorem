import PlattPointSubsetKernel
import PlattPointPackets.S7B000143
import PlattPointPackets.S7B000144
import PlattPointPackets.S7B000145
import PlattPointPackets.S7B000146
import PlattPointPackets.S7B000147
import PlattPointPackets.S7B000148
import PlattPointPackets.S7B000149
import PlattPointPackets.S7B000150
import PlattPointPackets.S7B000151
import PlattPointPackets.S7B000152
import PlattPointPackets.S7B000153
import PlattPointPackets.S7B000154
import PlattPointPackets.S7B000155
import PlattPointPackets.S7B000156
import PlattPointPackets.S7B000157
import PlattPointPackets.S7B000158
import PlattPointPackets.S7B000159
import PlattPointPackets.S7B000160
import PlattGlobalGrid.S8B000096
namespace ChenEffective.PlattWindow.PointCovers.S8B000096
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def sourcePoints : List PrimePoint := (((((((((((((((((ChenEffective.PlattWindow.PointPackets.S7B000143.points ++ ChenEffective.PlattWindow.PointPackets.S7B000144.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000145.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000146.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000147.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000148.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000149.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000150.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000151.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000152.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000153.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000154.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000155.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000156.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000157.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000158.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000159.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000160.points)
theorem checked : checkPointCoverAux 1000000 sourcePoints ChenEffective.PlattWindow.GlobalGrid.S8B000096.points=true := by decide +kernel
theorem covered : PointSubset ChenEffective.PlattWindow.GlobalGrid.S8B000096.points sourcePoints := .checked checked
#print axioms covered
end ChenEffective.PlattWindow.PointCovers.S8B000096
