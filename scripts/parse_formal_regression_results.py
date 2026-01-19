#!/usr/bin/env python3
"""
Formal Verification Results Parser

This script parses VCF formal verification results from run/formal/results/
directory and generates a unified summary for GitHub Actions.
"""

import os
import re
import sys

class AssertionStats(object):
    """Statistics for assertion properties"""
    
    def __init__(self):
        self.found = 0
        self.proven = 0
        self.failed = 0
        self.inconclusive = 0
        self.vacuous = 0


class CoverStats(object):
    """Statistics for cover properties"""
    
    def __init__(self):
        self.found = 0
        self.covered = 0


class DisabledStats(object):
    """Statistics for disabled properties"""
    
    def __init__(self):
        self.found = 0


class ModuleResults(object):
    """Results for a single module"""
    
    def __init__(self, module_name):
        self.module_name = module_name
        self.assertions = AssertionStats()
        self.covers = CoverStats()
        self.disabled = DisabledStats()
        self.total_properties = 0


class FormalResultsParser(object):
    """Parser for VCF formal verification results"""
    
    def __init__(self, formal_results_dir="run/formal/results"):
        self.formal_results_dir = formal_results_dir
        self.module_results = {}
    
    def find_modules(self):
        """Find all modules that have formal verification results"""
        modules = []
        if not os.path.exists(self.formal_results_dir):
            return modules
        
        for item in os.listdir(self.formal_results_dir):
            if item.endswith("_results.txt"):
                module_name = item[:-12]  # Remove "_results.txt"
                modules.append(module_name)
        
        return sorted(modules)
    
    def parse_summary_section(self, content, module_name):
        """Parse the Summary Results section"""
        results = ModuleResults(module_name)
        
        # Find the Summary Results section
        summary_match = re.search(r'Summary Results.*?Property Summary: FPV.*?(?=List Results|$)', content, re.DOTALL)
        if not summary_match:
            return results
        
        summary_section = summary_match.group(0)
        
        # Parse Assertion section
        assertion_section = re.search(r'> Assertion(.*?)(?=> \w+|\Z)', summary_section, re.DOTALL)
        if assertion_section:
            results.assertions = self._parse_assertion_stats(assertion_section.group(1))
        
        # Parse Cover section
        cover_section = re.search(r'> Cover(.*?)(?=> \w+|\Z)', summary_section, re.DOTALL)
        if cover_section:
            results.covers = self._parse_cover_stats(cover_section.group(1))
        
        # Parse Disabled section
        disabled_section = re.search(r'> Disabled(.*?)(?=> \w+|\Z)', summary_section, re.DOTALL)
        if disabled_section:
            results.disabled = self._parse_disabled_stats(disabled_section.group(1))
        
        # Calculate total properties
        results.total_properties = (results.assertions.found + results.covers.found + 
                                   results.disabled.found)
        
        return results
    
    def _parse_assertion_stats(self, section):
        """Parse statistics from assertion section"""
        stats = AssertionStats()
        
        patterns = {
            'found': r'# found\s*:\s*(\d+)',
            'proven': r'# proven\s*:\s*(\d+)',
            'failed': r'# falsified\s*:\s*(\d+)',
            'inconclusive': r'# inconclusive\s*:\s*(\d+)',
            'vacuous': r'# vacuous\s*:\s*(\d+)',
        }
        
        for field_name, pattern in patterns.items():
            match = re.search(pattern, section)
            if match:
                setattr(stats, field_name, int(match.group(1)))
        
        return stats
    
    def _parse_cover_stats(self, section):
        """Parse statistics from cover section"""
        stats = CoverStats()
        
        patterns = {
            'found': r'# found\s*:\s*(\d+)',
            'covered': r'# covered\s*:\s*(\d+)',
        }
        
        for field_name, pattern in patterns.items():
            match = re.search(pattern, section)
            if match:
                setattr(stats, field_name, int(match.group(1)))
        
        return stats
    
    def _parse_disabled_stats(self, section):
        """Parse statistics from disabled section"""
        stats = DisabledStats()
        
        match = re.search(r'# assert\s*:\s*(\d+)', section)
        if match:
            stats.found = int(match.group(1))
        
        return stats
    
    def parse_module_results(self, module_name):
        """Parse results for a specific module"""
        results_file = os.path.join(self.formal_results_dir, f"{module_name}_results.txt")
        
        try:
            with open(results_file, 'r') as f:
                content = f.read()
            
            return self.parse_summary_section(content, module_name)
        
        except Exception as e:
            print("Error parsing results for module {}: {}".format(module_name, e))
            return None
    
    def parse_all_modules(self):
        """Parse results for all modules"""
        modules = self.find_modules()
        parsing_errors = 0
        
        for module in modules:
            result = self.parse_module_results(module)
            if result:
                self.module_results[module] = result
            else:
                parsing_errors += 1
        
        return self.module_results, parsing_errors
    
    def _calculate_assertion_totals(self):
        """Calculate total assertion statistics across all modules"""
        totals = AssertionStats()
        
        for module_result in self.module_results.values():
            totals.found += module_result.assertions.found
            totals.proven += module_result.assertions.proven
            totals.failed += module_result.assertions.failed
            totals.inconclusive += module_result.assertions.inconclusive
            totals.vacuous += module_result.assertions.vacuous
        
        return totals
    
    def _calculate_cover_totals(self):
        """Calculate total cover statistics across all modules"""
        totals = CoverStats()
        
        for module_result in self.module_results.values():
            totals.found += module_result.covers.found
            totals.covered += module_result.covers.covered
        
        return totals
    
    def _calculate_disabled_totals(self):
        """Calculate total disabled statistics across all modules"""
        totals = DisabledStats()
        
        for module_result in self.module_results.values():
            totals.found += module_result.disabled.found
        
        return totals
    
    def generate_markdown_summary(self):
        """Generate a markdown summary for GitHub Actions"""
        if not self.module_results:
            return "## Formal Verification Results\n\nNo formal verification results found."
        
        totals = self._calculate_assertion_totals()
        
        md = ["## Formal Verification Results\n"]
        
        # Assertion properties summary
        md.append("### Assertions Summary")
        md.append("| Metric | Count |")
        md.append("|--------|-------|")
        md.append(f"| **Total Properties** | {totals.found} |")
        md.append(f"| ✅ **Proven** | {totals.proven} |")
        md.append(f"| ❌ **Falsified** | {totals.failed} |")
        md.append(f"| ⚠️ **Inconclusive** | {totals.inconclusive} |")
        md.append(f"| 🔄 **Vacuous** | {totals.vacuous} |")
        md.append("")
        
        # Success rate
        if totals.found > 0:
            success_rate = (totals.proven / float(totals.found)) * 100
            md.append("**Success Rate:** {:.1f}% ({}/{})\n".format(success_rate, totals.proven, totals.found))
        
        # Per-module breakdown
        if totals.found > 0:
            md.append("### Assert Properties by Module")
            md.append("| Module | Properties | Proven | Falsified | Inconclusive | Vacuous |")
            md.append("|--------|------------|--------|--------|--------------|---------|")
        
            for module_name in sorted(self.module_results.keys()):
                result = self.module_results[module_name]
                md.append("| `{}` | {} | {} | {} | {} | {} |".format(
                    module_name, result.assertions.found, result.assertions.proven,
                    result.assertions.failed, result.assertions.inconclusive, 
                    result.assertions.vacuous))
        
        md.append("")
        
        # Cover Properties Summary
        md.append("### Cover Properties Summary")
        cover_totals = self._calculate_cover_totals()
        md.append("| Metric | Count |")
        md.append("|--------|-------|")
        md.append(f"| **Total Covers** | {cover_totals.found} |")
        md.append(f"| ✅ **Covered** | {cover_totals.covered} |")
        md.append("")
        
        if cover_totals.found > 0:
            cover_rate = (cover_totals.covered / float(cover_totals.found)) * 100
            md.append("**Coverage Rate:** {:.1f}% ({}/{})\n".format(cover_rate, cover_totals.covered, cover_totals.found))
        
        # Per-module cover breakdown
        if cover_totals.found > 0:
            md.append("### Cover Properties by Module")
            md.append("| Module | Total Covers | Covered |")
            md.append("|--------|--------------|---------|")
            
            for module_name in sorted(self.module_results.keys()):
                result = self.module_results[module_name]
                if result.covers.found > 0:  # Only show modules that have covers
                    md.append("| `{}` | {} | {} |".format(
                        module_name, result.covers.found, result.covers.covered))
        
        md.append("")
        
        # Disabled Properties Summary
        md.append("### Disabled Properties Summary")
        disabled_totals = self._calculate_disabled_totals()
        md.append("| Metric | Count |")
        md.append("|--------|-------|")
        md.append(f"| ⛔ **Total Disabled** | {disabled_totals.found} |")
        md.append("")
        
        # Per-module disabled breakdown
        if disabled_totals.found > 0:
            md.append("### Disabled Properties by Module")
            md.append("| Module | Disabled |")
            md.append("|--------|----------|")
            
            for module_name in sorted(self.module_results.keys()):
                result = self.module_results[module_name]
                if result.disabled.found > 0:  # Only show modules that have disabled properties
                    md.append("| `{}` | {} |".format(
                        module_name, result.disabled.found))
        
        md.append("")
        
        return "\n".join(md)


def main():
    """Main entry point"""
    parser = FormalResultsParser()
    
    # Parse all results
    results, parsing_errors = parser.parse_all_modules()
    
    if not results:
        print("No formal verification results found.")
        sys.exit(1)
    
    # Generate and print markdown summary
    print(parser.generate_markdown_summary())
    
    # Print status indicators and exit with appropriate code
    totals = parser._calculate_assertion_totals()
    cover_totals = parser._calculate_cover_totals()
    
    if parsing_errors > 0:
        print("\n❌ **Parsing errors detected**")
        sys.exit(1)
    elif totals.failed > 0:
        print("\n❌ **Some properties were falsified**")
        sys.exit(1)
    elif totals.vacuous > 0:
        print("\n❌ **Some properties are vacuous**")
        sys.exit(1)
    elif totals.inconclusive > 0:
        print("\n⚠️ **Some properties are inconclusive**")
        sys.exit(1)
    elif (cover_totals.found - cover_totals.covered) > 0:
        print("\n❌ **Some cover properties are uncovered**")
        sys.exit(1)
    else:
        print("\n✅ **All properties verified successfully**")
        sys.exit(0)


if __name__ == "__main__":
    main()