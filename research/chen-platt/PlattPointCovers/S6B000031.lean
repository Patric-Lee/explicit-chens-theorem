import PlattPointSubsetKernel
import PlattPointPackets.S1B000383
import PlattPointPackets.S1B000384
import PlattPointPackets.S1B000385
import PlattPointPackets.S1B000386
import PlattGlobalGrid.S6B000031
namespace ChenEffective.PlattWindow.PointCovers.S6B000031
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def sourcePoints : List PrimePoint := (((ChenEffective.PlattWindow.PointPackets.S1B000383.points ++ ChenEffective.PlattWindow.PointPackets.S1B000384.points) ++ ChenEffective.PlattWindow.PointPackets.S1B000385.points) ++ ChenEffective.PlattWindow.PointPackets.S1B000386.points)
theorem checked : checkPointCoverAux 1000000 sourcePoints ChenEffective.PlattWindow.GlobalGrid.S6B000031.points=true := by decide +kernel
theorem covered : PointSubset ChenEffective.PlattWindow.GlobalGrid.S6B000031.points sourcePoints := .checked checked
#print axioms covered
end ChenEffective.PlattWindow.PointCovers.S6B000031
