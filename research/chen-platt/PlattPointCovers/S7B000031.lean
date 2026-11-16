import PlattPointSubsetKernel
import PlattPointPackets.S2B000152
import PlattPointPackets.S2B000153
import PlattPointPackets.S2B000154
import PlattPointPackets.S2B000155
import PlattPointPackets.S2B000156
import PlattGlobalGrid.S7B000031
namespace ChenEffective.PlattWindow.PointCovers.S7B000031
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def sourcePoints : List PrimePoint := ((((ChenEffective.PlattWindow.PointPackets.S2B000152.points ++ ChenEffective.PlattWindow.PointPackets.S2B000153.points) ++ ChenEffective.PlattWindow.PointPackets.S2B000154.points) ++ ChenEffective.PlattWindow.PointPackets.S2B000155.points) ++ ChenEffective.PlattWindow.PointPackets.S2B000156.points)
theorem checked : checkPointCoverAux 1000000 sourcePoints ChenEffective.PlattWindow.GlobalGrid.S7B000031.points=true := by decide +kernel
theorem covered : PointSubset ChenEffective.PlattWindow.GlobalGrid.S7B000031.points sourcePoints := .checked checked
#print axioms covered
end ChenEffective.PlattWindow.PointCovers.S7B000031
