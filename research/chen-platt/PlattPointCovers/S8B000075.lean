import PlattPointSubsetKernel
import PlattPointPackets.S6B000142
import PlattPointPackets.S6B000143
import PlattPointPackets.S6B000144
import PlattPointPackets.S6B000145
import PlattPointPackets.S6B000146
import PlattPointPackets.S6B000147
import PlattPointPackets.S6B000148
import PlattPointPackets.S6B000149
import PlattPointPackets.S6B000150
import PlattPointPackets.S6B000151
import PlattPointPackets.S6B000152
import PlattPointPackets.S6B000153
import PlattPointPackets.S6B000154
import PlattPointPackets.S6B000155
import PlattPointPackets.S6B000156
import PlattGlobalGrid.S8B000075
namespace ChenEffective.PlattWindow.PointCovers.S8B000075
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def sourcePoints : List PrimePoint := ((((((((((((((ChenEffective.PlattWindow.PointPackets.S6B000142.points ++ ChenEffective.PlattWindow.PointPackets.S6B000143.points) ++ ChenEffective.PlattWindow.PointPackets.S6B000144.points) ++ ChenEffective.PlattWindow.PointPackets.S6B000145.points) ++ ChenEffective.PlattWindow.PointPackets.S6B000146.points) ++ ChenEffective.PlattWindow.PointPackets.S6B000147.points) ++ ChenEffective.PlattWindow.PointPackets.S6B000148.points) ++ ChenEffective.PlattWindow.PointPackets.S6B000149.points) ++ ChenEffective.PlattWindow.PointPackets.S6B000150.points) ++ ChenEffective.PlattWindow.PointPackets.S6B000151.points) ++ ChenEffective.PlattWindow.PointPackets.S6B000152.points) ++ ChenEffective.PlattWindow.PointPackets.S6B000153.points) ++ ChenEffective.PlattWindow.PointPackets.S6B000154.points) ++ ChenEffective.PlattWindow.PointPackets.S6B000155.points) ++ ChenEffective.PlattWindow.PointPackets.S6B000156.points)
theorem checked : checkPointCoverAux 1000000 sourcePoints ChenEffective.PlattWindow.GlobalGrid.S8B000075.points=true := by decide +kernel
theorem covered : PointSubset ChenEffective.PlattWindow.GlobalGrid.S8B000075.points sourcePoints := .checked checked
#print axioms covered
end ChenEffective.PlattWindow.PointCovers.S8B000075
